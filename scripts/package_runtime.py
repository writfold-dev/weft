#!/usr/bin/env python3
"""Package one qualified musl binary in the scratch runtime image and exercise it.

Packaging is separate from `scripts/gate rust`: this consumes a passing Rust
receipt's retained executable and Cargo metadata, collects dependency notices
with `scripts/package_licenses.py`, builds `docker/Dockerfile.runtime` in an
owned context, verifies the exported root filesystem, and runs positive and
refusal cases read-only, network-disabled and capability-free. It never
publishes, prunes or touches resources it did not create.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import uuid

sys.dont_write_bytecode = True
from evidence import capture_sources, digest, manifest, process_env, require_success, run_logged, write_new
from preflight import observe

ROOT = Path(__file__).resolve().parent.parent
STATE = Path.home() / ".local/share/weft"
PRODUCER = ["scripts/package_runtime.py", "scripts/package_licenses.py", "scripts/evidence.py",
            "scripts/preflight.py", "docker/Dockerfile.runtime", "LICENSE", "compose.yaml",
            "toolchains.lock.json", "examples/set-algebra.weft", "examples/sets.weft"]
SCOPE = ("static local-symbolic artifact (set algebra, local reuse gate, pinned writfold control "
         "client, weft-core kernel) in a non-root scratch image; composed Writfold release remains blocked")
HARDENING = ["--network=none", "--read-only", "--cap-drop=ALL",
             "--security-opt=no-new-privileges:true", "--pids-limit=32",
             "--memory=268435456", "--cpus=1", "--platform=linux/amd64"]
# Empty placeholders Docker adds to every exported container filesystem.
RUNTIME_INJECTED = {".dockerenv", "dev/console", "etc/hostname", "etc/hosts", "etc/resolv.conf"}
ROOTFS = {"weft": 0o555, "LICENSE": 0o444,
          "licenses/third-party-licenses.zip": 0o444, "licenses/third-party-licenses.json": 0o444}


def home_relative(path: Path) -> str:
    path = path.resolve()
    return f"~/{path.relative_to(Path.home())}" if path.is_relative_to(Path.home()) else str(path)


def inspect(reference: str) -> dict:
    return json.loads(subprocess.check_output(["docker", "image", "inspect", reference],
                                              text=True, timeout=30))[0]


def qualified_runtime(receipt: Path) -> tuple[dict, dict]:
    report = json.loads(receipt.read_text())
    producer = report["result"]["producer"]
    if (report["status"] != "pass" or report["gate"] != "rust"
            or report["scope"] != "weft-local-symbolic-runtime-only"
            or producer["status"] != "pass" or producer["skipped"]):
        raise ValueError("Rust receipt is not a complete local runtime pass")
    if digest(receipt.parent / "weft") != producer["binary_sha256"]:
        raise ValueError("retained musl executable differs from its Rust receipt")
    closure = report["result"]["source_manifest"]
    for path in ("docker/Dockerfile.runtime", "LICENSE"):
        if closure.get(path) != digest(ROOT / path):
            raise ValueError(f"packaging input differs from the qualified Rust closure: {path}")
    admission = json.loads((STATE / "tool-admission.json").read_text())
    if admission["image_id"] != report["result"]["image_id"] or inspect(admission["image_id"])["Id"] != admission["image_id"]:
        raise ValueError("admitted tool image differs from the Rust receipt's image")
    return report, producer


def collect_licenses(attempt: Path, rust_dir: Path, image: str) -> dict:
    for label in ("workspace-metadata", "policy-metadata"):
        source = rust_dir / f"{label}.stdout"
        shutil.copyfile(source, attempt / f"{label}.json")
        if digest(attempt / f"{label}.json") != digest(source):
            raise ValueError(f"copied Cargo metadata differs: {label}")
    name = f"weft-license-{uuid.uuid4().hex}"
    try:
        record = run_logged([
            "docker", "compose", "run", "--rm", "--name", name, "qualify",
            "timeout", "--signal=TERM", "--kill-after=30", "600", "python3", "scripts/package_licenses.py",
        ], ROOT, attempt, "collect-licenses",
            env=process_env(WEFT_TOOL_IMAGE=image, WEFT_ATTEMPT=str(attempt)), timeout=700)
        require_success(record)
    finally:
        subprocess.run(["docker", "rm", "--force", name], capture_output=True, check=False)
    notices = json.loads((attempt / "third-party-licenses.json").read_text())
    if notices["archive_sha256"] != digest(attempt / "third-party-licenses.zip"):
        raise ValueError("notice inventory does not bind its archive")
    return {"archive_sha256": notices["archive_sha256"], "packages": len(notices["packages"]),
            "inventory_sha256": digest(attempt / "third-party-licenses.json"), "command": record}


def build(attempt: Path, rust_dir: Path, binary: str) -> tuple[str, str, dict[str, str]]:
    context = attempt / "context"
    context.mkdir()
    shutil.copy2(rust_dir / "weft", context / "weft")
    shutil.copyfile(ROOT / "LICENSE", context / "LICENSE")
    for name in ("third-party-licenses.zip", "third-party-licenses.json"):
        shutil.copyfile(attempt / name, context / name)
    if digest(context / "weft") != binary:
        raise ValueError("packaging context binary differs from the qualified executable")
    expected = {"weft": binary, "LICENSE": digest(context / "LICENSE"),
                "licenses/third-party-licenses.zip": digest(context / "third-party-licenses.zip"),
                "licenses/third-party-licenses.json": digest(context / "third-party-licenses.json")}
    tag = f"weft-runtime:sha256-{binary[:16]}-{uuid.uuid4().hex[:8]}"
    require_success(run_logged([
        "docker", "buildx", "build", "--network=none", "--pull=false", "--load",
        "--platform=linux/amd64", "--file", str(ROOT / "docker/Dockerfile.runtime"),
        "--iidfile", str(attempt / "image.iid"), "--tag", tag, str(context),
    ], ROOT, attempt, "buildkit-runtime", timeout=600))
    image_id = (attempt / "image.iid").read_text().strip()
    require_success(run_logged(["docker", "image", "inspect", image_id], ROOT, attempt, "image-identity"))
    config = json.loads((attempt / "image-identity.stdout").read_text())[0]
    if (config["Id"] != image_id or config["Os"] != "linux" or config["Architecture"] != "amd64"
            or config["Config"]["User"] != "65532:65532" or config["Config"]["Entrypoint"] != ["/weft"]):
        raise ValueError("scratch image identity, platform, user or entrypoint differs")
    return image_id, tag, expected


def verify_rootfs(attempt: Path, image_id: str, expected: dict[str, str]) -> dict:
    name = f"weft-runtime-inspect-{uuid.uuid4().hex}"
    try:
        require_success(run_logged(["docker", "create", "--name", name, image_id], ROOT, attempt, "rootfs-create"))
        require_success(run_logged(["docker", "export", "--output", str(attempt / "rootfs.tar"), name],
                                   ROOT, attempt, "rootfs-export"))
    finally:
        subprocess.run(["docker", "rm", "--force", name], capture_output=True, check=False)
    observed = {}
    with tarfile.open(attempt / "rootfs.tar") as archive:
        for member in archive.getmembers():
            if not member.isfile():
                continue
            key = member.name.removeprefix("./")
            if key in RUNTIME_INJECTED and member.size == 0:
                continue
            if key not in ROOTFS:
                raise ValueError(f"unexpected regular file in scratch image: {key}")
            if member.mode & 0o7777 != ROOTFS[key]:
                raise ValueError(f"scratch file mode differs: {key}")
            stream = archive.extractfile(member)
            observed[key] = hashlib.sha256(stream.read()).hexdigest()
    if observed != expected:
        raise ValueError("exported scratch files differ from the packaged inputs")
    return {"files": observed, "tar_sha256": digest(attempt / "rootfs.tar")}


def scratch(attempt: Path, image_id: str, label: str, args: list[str], exit_code: int) -> dict:
    inputs = attempt / "inputs"
    name = f"weft-runtime-{uuid.uuid4().hex}"
    try:
        record = run_logged([
            "docker", "run", "--rm", "--name", name, *HARDENING,
            "--mount", f"type=bind,source={inputs},target=/inputs,readonly",
            image_id, *args,
        ], ROOT, attempt, label, timeout=120)
    finally:
        subprocess.run(["docker", "rm", "--force", name], capture_output=True, check=False)
    if record["exit_code"] != exit_code:
        raise ValueError(f"scratch case exit differs: {label}")
    return {"argv": args, "exit_code": record["exit_code"], "command": record}


def exercise(attempt: Path, image_id: str, rust_dir: Path, producer: dict) -> dict:
    inputs = attempt / "inputs"
    inputs.mkdir(mode=0o755)
    expected = {case["id"]: case for case in producer["smoke"]["cases"]}
    cases = {"version": scratch(attempt, image_id, "scratch-version", ["--version"], 0)}
    version = (attempt / "scratch-version.stdout").read_text()
    if (version != (rust_dir / "binary-version.stdout").read_text()
            or "profile=weft.symbolic/1" not in version
            or "writfold_grounded=false effect_authority=false" not in version):
        raise ValueError("scratch --version differs from the qualified binary's identity line")
    for example in ("set-algebra", "sets"):
        source = ROOT / f"examples/{example}.weft"
        shutil.copyfile(source, inputs / f"{example}.weft")
        (inputs / f"{example}.weft").chmod(0o644)
        smoke = expected[f"example-{example}"]
        if digest(inputs / f"{example}.weft") != smoke["source_sha256"]:
            raise ValueError(f"example differs from the Rust receipt's smoke input: {example}")
        label = f"scratch-{example}"
        case = scratch(attempt, image_id, label, ["prove", f"/inputs/{example}.weft"], smoke["exit_code"])
        report = json.loads((attempt / f"{label}.stdout").read_text())
        verdicts = [check["result"] for check in report["checks"]]
        if (verdicts != smoke["results"] or report["writfold_grounded"] is not False
                or report["effect_authority"] is not False
                or report["source"]["sha256"] != smoke["source_sha256"]):
            raise ValueError(f"scratch report differs from the qualified smoke result: {example}")
        case["verdicts"] = verdicts
        case["source_sha256"] = smoke["source_sha256"]
        cases[f"{example}-positive"] = case
    cases["missing-source-refusal"] = scratch(
        attempt, image_id, "scratch-missing", ["prove", "/inputs/absent.weft"], 2)
    cases["invalid-command-refusal"] = scratch(
        attempt, image_id, "scratch-bogus", ["bogus"], 2)
    return cases


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-receipt", required=True, type=Path)
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args()
    receipt = args.receipt.expanduser().resolve()
    rust_receipt = args.rust_receipt.expanduser().resolve()
    if receipt.is_relative_to(ROOT):
        parser.error("receipts must be outside the source checkout")
    receipt.parent.mkdir(parents=True, exist_ok=False)
    attempt = receipt.parent
    record: dict[str, object] = {"schema_version": 1, "status": "fail", "scope": SCOPE}
    try:
        record["producer_snapshot"] = capture_sources(ROOT, PRODUCER, attempt / "producer-source.zip")
        record["preflight"] = observe(ROOT)
        report, producer = qualified_runtime(rust_receipt)
        record["binary_sha256"] = producer["binary_sha256"]
        record["rust_receipt"] = home_relative(rust_receipt)
        record["rust_receipt_sha256"] = digest(rust_receipt)
        record["dockerfile_sha256"] = digest(ROOT / "docker/Dockerfile.runtime")
        record["license_packaging"] = collect_licenses(attempt, rust_receipt.parent, report["result"]["image_id"])
        image_id, tag, expected = build(attempt, rust_receipt.parent, producer["binary_sha256"])
        record["image_id"], record["image_tag"] = image_id, tag
        record["rootfs"] = verify_rootfs(attempt, image_id, expected)
        record["scratch_cases"] = exercise(attempt, image_id, rust_receipt.parent, producer)
        record["security"] = {"user": "65532:65532", "read_only": True, "network": "none",
                              "capabilities": "dropped (ALL)", "no_new_privileges": True,
                              "pids_limit": 32, "memory_bytes": 268435456, "cpus": 1,
                              "inputs_mount": "read-only bind of copied example sources"}
        if record["producer_snapshot"]["sources"] != manifest(ROOT, PRODUCER):
            raise ValueError("packaging producer changed while executing")
        record["status"] = "pass"
    except (OSError, ValueError, KeyError, subprocess.SubprocessError, tarfile.TarError) as error:
        record["error"] = f"{type(error).__name__}: {error}"
    write_new(receipt, record)
    print(json.dumps({"status": record["status"], "receipt": str(receipt)}, indent=2))
    return 0 if record["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
