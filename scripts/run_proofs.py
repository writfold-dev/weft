"""Run a clean Lean build, complete audit, real reference cases and mutations."""
from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
import json
from pathlib import Path
import re
import shutil
import tempfile

from evidence import digest, manifest, require_success, run_logged, write_new
from contracts import reconcile

ROOT = Path("/work/weft")
EVIDENCE = Path("/evidence")
CACHE = Path("/cache/target/lean-4.21.0")


@contextmanager
def clean_copy(label: str) -> Iterator[Path]:
    CACHE.mkdir(parents=True, exist_ok=True)
    owned = Path(tempfile.mkdtemp(prefix=f"{label}-", dir=CACHE))
    target = owned / "formal"
    try:
        shutil.copytree(ROOT / "formal", target, ignore=shutil.ignore_patterns(".lake"))
        yield target
    finally:
        shutil.rmtree(owned)


def audit(source: Path) -> dict[str, list[str]]:
    policy = json.loads((ROOT / "formal/audit-targets.json").read_text())
    names = reconcile(ROOT)["audit_declarations"]
    audit_file = EVIDENCE / "Audit.lean"
    audit_file.write_text("import Weft\nimport Weft.Composition\n" + "\n".join(
        f"#check {name}\n#print axioms {name}" for name in names
    ) + "\n")
    require_success(run_logged(
        ["lake", "env", "lean", str(audit_file)], source, EVIDENCE, "axiom-audit",
    ))
    found: dict[str, list[str]] = {}
    for line in (EVIDENCE / "axiom-audit.stdout").read_text().splitlines():
        empty = re.fullmatch(r"'([^']+)' does not depend on any axioms", line.strip())
        present = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line.strip())
        if empty:
            found[empty[1]] = []
        elif present:
            found[present[1]] = [part.strip() for part in present[2].split(",") if part.strip()]
    if set(found) != set(names):
        raise ValueError(f"missing/unexpected axiom-audit declarations: {set(names) ^ set(found)}")
    allowed = set(policy["allowed_foundational_axioms"])
    for name, axioms in found.items():
        if set(axioms) - allowed:
            raise ValueError(f"unadmitted axioms in {name}: {axioms}")
    return found


def reference_cases(source: Path) -> list[dict]:
    atom = lambda index: {"kind": "atom", "index": index}
    neg = lambda inner: {"kind": "not", "inner": inner}
    literal = lambda value: {"kind": "literal", "value": value}
    cases = [
        ("entailed", 1, [atom(0)], atom(0), 2, "entailed"),
        ("refuted", 1, [neg(atom(0))], atom(0), 2, "refuted"),
        ("wrong-polarity", 1, [atom(0)], neg(atom(0)), 2, "refuted"),
        ("two-models", 1, [], atom(0), 2, "undetermined"),
        ("inconsistent", 1, [atom(0), neg(atom(0))], literal(True), 2, "inconsistent-premises"),
        ("no-budget", 1, [], atom(0), 1, "unknown"),
        ("invalid-domain", 0, [], atom(0), 1, "unknown"),
        ("empty-domain", 0, [], literal(False), 1, "refuted"),
    ]
    requests = [{"id": name, "atoms": atoms, "premises": premises,
                 "query": query, "budget": budget}
                for name, atoms, premises, query, budget, _ in cases]
    request_file = EVIDENCE / "reference-inputs.jsonl"
    request_file.write_text("".join(json.dumps(row) + "\n" for row in requests))
    binary = source / ".lake/build/bin/weftref"
    require_success(run_logged(
        [str(binary), str(request_file)], source, EVIDENCE, "reference-smoke",
    ))
    actual = [json.loads(line) for line in (EVIDENCE / "reference-smoke.stdout").read_text().splitlines()]
    expected = [{"id": row[0], "verdict": row[-1]} for row in cases]
    if actual != expected:
        raise ValueError(f"reference semantic results differ: {actual}")
    shutil.copy2(binary, EVIDENCE / "weftref")
    return actual


def mutate() -> list[dict]:
    mutations = json.loads((ROOT / "scripts/lean_mutations.json").read_text())["mutations"]
    registry = json.loads((ROOT / "handovers/revision-1/weft/registries/theorems.json").read_text())
    required_families = {item["id"] for item in registry["theorems"]}
    if {item["theorem_family"] for item in mutations} != required_families:
        raise ValueError("semantic mutation inventory omits or invents a required theorem family")
    identifiers = [item["id"] for item in mutations]
    if len(set(identifiers)) != len(identifiers):
        raise ValueError("duplicate semantic mutation identity")
    for mutation in mutations:
        if not re.fullmatch(r"M\d\d-[a-z0-9-]+", mutation["id"]):
            raise ValueError("invalid mutation identity")
        for key in ("file", "expected_error_file"):
            path = Path(mutation[key])
            if path.is_absolute() or ".." in path.parts or path.parts[0] != "Weft" or path.suffix != ".lean":
                raise ValueError("mutation must remain inside the owned Lean source namespace")
    results = []
    for mutation in mutations:
        with clean_copy(mutation["id"]) as source:
            target = source / mutation["file"]
            original = target.read_text()
            if original.count(mutation["search"]) != 1:
                raise ValueError(f"mutation anchor is not unique: {mutation['id']}")
            target.write_text(original.replace(mutation["search"], mutation["replacement"], 1))
            result = run_logged(["lake", "build", "Weft"], source, EVIDENCE, mutation["id"])
            text = (EVIDENCE / f"{mutation['id']}.stdout").read_text() + (EVIDENCE / f"{mutation['id']}.stderr").read_text()
            if result["exit_code"] == 0 or result["exit_code"] is None:
                raise ValueError(f"semantic mutant was not rejected: {mutation['id']}")
            expected_file = mutation["expected_error_file"]
            expected_errors = re.findall(
                rf"^error: {re.escape(expected_file)}:\d+:\d+: (.+)$", text, flags=re.MULTILINE,
            )
            substantive = [
                message for message in expected_errors
                if any(marker in message for marker in (
                    "unsolved goals", "type mismatch", "tactic", "invalid constructor",
                ))
            ]
            if not substantive:
                raise ValueError(f"mutant lacks a substantive proof failure at its target: {mutation['id']}")
            results.append({"id": mutation["id"], "status": "rejected", "changed_source": digest(target),
                            "expected_error_file": expected_file, "diagnostics": substantive})
    return results


def main() -> int:
    result: dict = {"schema_version": 1, "status": "fail", "scope": "weft-language-calculus-only", "skipped": []}
    try:
        with clean_copy("baseline") as source:
            require_success(run_logged(
                ["python3", "scripts/test_qualification.py"], ROOT, EVIDENCE,
                "qualification-boundaries",
            ))
            result["formal_source"] = manifest(ROOT, ["formal"])
            require_success(run_logged(["lake", "build"], source, EVIDENCE, "lean-build", timeout=900))
            result["axioms"] = audit(source)
            result["executed_reference_cases"] = reference_cases(source)
            result["mutants"] = mutate()
            result["reference_binary_sha256"] = digest(EVIDENCE / "weftref")
            result["status"] = "pass"
    except (OSError, ValueError, KeyError) as error:
        result["error"] = f"{type(error).__name__}: {error}"
    write_new(EVIDENCE / "lean-results.json", result)
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
