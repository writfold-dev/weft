#!/usr/bin/env python3
"""Derive the current runtime records from actual receipts; no counts or digests are typed.

`local` rewrites qualification/local-runtime.json from one passing Rust receipt,
its retained outputs and a passing scratch packaging receipt for the same
binary. Historical receipts already listed are carried forward and the record
being replaced joins `earlier_passes`.

`traceability` rebinds qualification/traceability.json: named receipt
references are re-hashed from their files, and every theorem/scenario
source or fixture digest is replaced by the Rust/formal closure digest only
when the current checkout bytes equal that qualified closure. Symbols,
requirements, statuses and scopes are not changed here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
from evidence import digest

ROOT = Path(__file__).resolve().parent.parent
TEST_RESULT = re.compile(r"test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored")


def home_relative(path: Path) -> str:
    path = path.expanduser().resolve()
    return f"~/{path.relative_to(Path.home())}" if path.is_relative_to(Path.home()) else str(path)


def load(path: Path) -> dict:
    return json.loads(path.expanduser().read_text())


def tests(directory: Path, label: str) -> dict[str, int]:
    text = (directory / f"{label}.stdout").read_text() + (directory / f"{label}.stderr").read_text()
    rows = [tuple(map(int, match)) for match in TEST_RESULT.findall(text)]
    if not rows:
        raise ValueError(f"no test harness results in {label}")
    totals = {"passed": sum(row[0] for row in rows), "failed": sum(row[1] for row in rows),
              "ignored": sum(row[2] for row in rows), "harnesses": len(rows)}
    if totals["failed"]:
        raise ValueError(f"failed tests recorded in {label}")
    return totals


def size_findings(directory: Path, label: str) -> dict[str, int]:
    findings = load(directory / f"{label}.stdout")["report"]["findings"]
    return {"warnings": sum(item["severity"] == "warning" for item in findings),
            "errors": sum(item["severity"] != "warning" for item in findings)}


def local(args: argparse.Namespace) -> None:
    rust_path = args.rust_receipt.expanduser().resolve()
    package_path = args.package_receipt.expanduser().resolve()
    rust, package = load(rust_path), load(package_path)
    directory = rust_path.parent
    result = rust["result"]
    producer = result["producer"]
    if rust["status"] != "pass" or producer["status"] != "pass" or producer["skipped"]:
        raise ValueError("Rust receipt is not a complete pass")
    binary = producer["binary_sha256"]
    if digest(directory / "weft") != binary or producer["smoke"]["binary_sha256"] != binary:
        raise ValueError("retained executable differs from the Rust receipt")
    if (package["status"] != "pass" or package["binary_sha256"] != binary
            or Path(package["rust_receipt"]).expanduser().resolve() != rust_path
            or package["rust_receipt_sha256"] != digest(rust_path)):
        raise ValueError("scratch packaging receipt does not bind this Rust receipt and binary")
    elf = (directory / "elf-file.stdout").read_text()
    if "static-pie linked" not in elf and "statically linked" not in elf:
        raise ValueError("retained executable is not statically linked")
    build = load(directory / "musl-build.command.json")
    if "x86_64-unknown-linux-musl" not in build["argv"]:
        raise ValueError("musl build target is not recorded")
    previous = load(ROOT / "qualification/local-runtime.json")
    if previous["receipt"] == home_relative(rust_path):
        raise ValueError("the current record already binds this Rust receipt")
    proof = result["proof_prerequisite"]
    smoke = producer["smoke"]
    cases = smoke["cases"]
    workspace, policy = tests(directory, "workspace-tests"), tests(directory, "policy-tests")
    nominal = producer["nominal_cases"]
    if not all(case["passed"] for case in nominal):
        raise ValueError("nominal control did not pass")
    earlier = [row for row in previous["earlier_passes"]]
    replaced = {"receipt": previous["receipt"], "sha256": previous["receipt_sha256"],
                "scope": args.replaced_scope}
    if all(row["receipt"] != replaced["receipt"] for row in earlier):
        earlier.append(replaced)
    failed = list(previous["failed_runtime_attempts"])
    for attempt in args.failed:
        path = attempt.expanduser().resolve()
        if load(path)["status"] == "pass":
            raise ValueError(f"a passing receipt cannot be indexed as failed: {path}")
        reference = {"receipt": home_relative(path), "sha256": digest(path)}
        if reference not in failed:
            failed.append(reference)
    record = {
        "schema_version": 1,
        "status": "pass",
        "scope": rust["scope"],
        "receipt": home_relative(rust_path),
        "receipt_sha256": digest(rust_path),
        "binary": {"path": home_relative(directory / "weft"), "sha256": binary,
                   "static": True, "triple": "x86_64-unknown-linux-musl",
                   "build_source_sha256": producer["binary_source_sha256"]},
        "tool_image_id": result["image_id"],
        "tool_lock_sha256": rust["tool_lock_sha256"],
        "proof_prerequisite": {
            "calculus_ledger": "qualification/finite-calculus.json",
            "calculus_sha256": result["source_manifest"]["qualification/finite-calculus.json"],
            "initial_calculus_receipt": proof["initial_calculus_receipt"],
            "initial_calculus_sha256": proof["initial_calculus_sha256"],
            "reference_ledger": "qualification/reference-calibration.json",
            "reference_ledger_sha256": result["source_manifest"]["qualification/reference-calibration.json"],
            "reference_receipt": home_relative(Path(proof["receipt"])),
            "reference_sha256": proof["sha256"],
        },
        "verification": {
            "derivation": "Counted from the Rust receipt's retained test, policy, nominal, lint and smoke outputs.",
            "behavioral_regressions": workspace["passed"],
            "policy_regressions": policy["passed"],
            "ignored_tests": workspace["ignored"] + policy["ignored"],
            "nominal_positive_controls": sum(case["expected_error"] is None for case in nominal),
            "nominal_negative_controls": sum(case["expected_error"] is not None for case in nominal),
            "operation_controls": len(producer["compiler_lint_calibration"]["cases"]),
            "source_size_soft_warnings": size_findings(directory, "workspace-ast-policy")["warnings"],
            "source_size_errors": size_findings(directory, "workspace-ast-policy")["errors"],
            "policy_tool_size_soft_warnings": size_findings(directory, "policy-ast-policy")["warnings"],
        },
        "cli_cases": {
            "smoke_cases": len(cases),
            "scenario_count": sum(not case["id"].startswith(("example-", "external-")) for case in cases),
            "examples": {case["id"].removeprefix("example-"): case["results"]
                         for case in cases if case["id"].startswith("example-")},
            "reuse_cases": len(smoke["reuse"]),
            "finite_reference_cases": len(smoke["finite_reference"]),
            "differential_checks": smoke["differential"]["checks"],
            "differential_witnesses": smoke["differential"]["witnesses"],
            "algebra_differential_pairs": len(smoke["algebra_differential"]["pairs"]),
        },
        "advisory_snapshot": producer["dependencies"]["advisory_snapshot"],
        "license_packaging": {
            "receipt": home_relative(package_path),
            "sha256": digest(package_path),
            "archive_sha256": package["license_packaging"]["archive_sha256"],
            "packages": package["license_packaging"]["packages"],
        },
        "scratch_runtime": {
            "receipt": home_relative(package_path),
            "sha256": digest(package_path),
            "image_id": package["image_id"],
            "binary_sha256": package["binary_sha256"],
            "cases": {name: case["exit_code"] for name, case in package["scratch_cases"].items()},
        },
        "source_manifest": result["source_manifest"],
        "earlier_passes": earlier,
        "failed_runtime_attempts": failed,
        "full_composed_release": previous["full_composed_release"],
        "limitations": previous["limitations"],
    }
    write(ROOT / "qualification/local-runtime.json", record, sort_keys=True)


def rebind(record: dict, closure: dict[str, str]) -> int:
    current = digest(ROOT / record["path"])
    if closure.get(record["path"]) != current:
        raise ValueError(f"current source is outside the qualified closure: {record['path']}")
    changed = int(record["sha256"] != current)
    record["sha256"] = current
    return changed


def traceability(args: argparse.Namespace) -> None:
    path = ROOT / "qualification/traceability.json"
    data = json.loads(path.read_text())
    scopes = dict(item.split("=", 1) for item in args.scope)
    for item in args.bind:
        name, location = item.split("=", 1)
        reference = data["receipts"].setdefault(name, {})
        file = Path(location).expanduser()
        if not file.is_absolute():
            file = ROOT / file
        reference["path"] = location
        reference["sha256"] = digest(file)
        if name in scopes:
            reference["scope"] = scopes.pop(name)
    if scopes:
        raise ValueError(f"scope given for an unbound receipt: {sorted(scopes)}")
    receipt = lambda name: load(Path(data["receipts"][name]["path"]))
    rust_sources = receipt("rust-runtime")["result"]["source_manifest"]
    formal_sources = receipt("finite-reference")["result"]["producer"]["formal_source"]
    changed = 0
    for row in data["theorems"]:
        changed += rebind(row["lean_source"], formal_sources)
        for symbol in row["rust"]:
            changed += rebind(symbol, rust_sources)
        for fixture in row["fixtures"]:
            changed += rebind(fixture, rust_sources | formal_sources)
    for row in data["scenarios"]:
        for fixture in row["fixtures"]:
            changed += rebind(fixture, rust_sources | formal_sources)
    write(path, data)
    print(json.dumps({"rebound_source_digests": changed}))


def write(path: Path, value: dict, *, sort_keys: bool = False) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=sort_keys) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    runtime = commands.add_parser("local")
    runtime.add_argument("--rust-receipt", required=True, type=Path)
    runtime.add_argument("--package-receipt", required=True, type=Path)
    runtime.add_argument("--replaced-scope", required=True)
    runtime.add_argument("--failed", action="append", default=[], type=Path)
    trace = commands.add_parser("traceability")
    trace.add_argument("--bind", action="append", default=[], help="NAME=PATH")
    trace.add_argument("--scope", action="append", default=[], help="NAME=TEXT")
    args = parser.parse_args()
    (local if args.command == "local" else traceability)(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
