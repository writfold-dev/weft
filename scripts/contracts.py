"""Reconcile active immutable requirements before executing any qualification."""
from __future__ import annotations

import json
from pathlib import Path
import re

from evidence import digest, manifest


def reconcile(root: Path) -> dict[str, object]:
    adoption_path = root / "qualification/handover-adoption.json"
    adoption = json.loads(adoption_path.read_text())
    relative = Path(adoption["authority"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("handover authority must remain inside the source root")
    authority = root / relative
    # Validate every component of the configured authority path, including links.
    manifest(root, [str(relative / "MANIFEST.sha256")])
    manifest_path = authority / "MANIFEST.sha256"
    if digest(manifest_path) != adoption["manifest_sha256"]:
        raise ValueError("handover manifest differs from active adoption")
    expected: dict[str, str] = {}
    for line in manifest_path.read_text().splitlines():
        checksum, separator, name = line.partition("  ")
        path = Path(name)
        if (not separator or not re.fullmatch(r"[0-9a-f]{64}", checksum)
                or path.is_absolute() or ".." in path.parts or name in expected):
            raise ValueError("malformed/duplicate immutable manifest entry")
        expected[name] = checksum
    observed = {}
    for path in sorted(authority.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"symlink in immutable handover: {path}")
        if path.is_file() and path != manifest_path:
            observed[str(path.relative_to(authority))] = digest(path)
    if observed != expected:
        raise ValueError("immutable handover members or bytes differ from its manifest")
    gates = json.loads((authority / "registries/gates.json").read_text())["stages"]
    theorems = json.loads((authority / "registries/theorems.json").read_text())["theorems"]
    inventory = adoption["inventory"]
    ids = [entry["id"] for entry in gates]
    gate_ids = [entry["gate"] for entry in gates]
    declarations = [entry["declaration"] for entry in theorems]
    if (len(ids) != inventory["stages"] or len(set(ids)) != len(ids)
            or len(gate_ids) != inventory["gates"] or len(set(gate_ids)) != len(gate_ids)
            or len(declarations) != inventory["language_theorems"]
            or len(set(declarations)) != len(declarations)):
        raise ValueError("stage/gate/theorem inventory differs from adoption")
    seen = set()
    for stage in gates:
        if stage["required"] is not True or not set(stage["dependencies"]) <= seen:
            raise ValueError("invalid required stage or dependency order")
        seen.add(stage["id"])
    if any(theorem["required"] is not True for theorem in theorems):
        raise ValueError("required language theorem was weakened")
    source_contract = adoption["source_contract_inputs"]
    if manifest(root, list(source_contract)) != source_contract:
        raise ValueError("active language/report contract inputs changed without adoption")
    profile_binding = adoption["proof_profile"]
    profile_path = profile_binding["path"]
    if manifest(root, [profile_path])[profile_path] != profile_binding["sha256"]:
        raise ValueError("expanded proof audit profile changed without adoption")
    policy = json.loads((root / profile_path).read_text())
    if policy["required_registry"] != str(relative / "registries/theorems.json"):
        raise ValueError("proof audit selected a different mandatory theorem registry")
    extra = policy["additional_declarations"]
    audited = declarations + extra
    if (len(extra) != profile_binding["additional_declarations"]
            or len(set(audited)) != len(audited)
            or any(not re.fullmatch(r"Weft\.[A-Za-z0-9_.]+", name) for name in audited)):
        raise ValueError("expanded proof declaration inventory is invalid")
    if set(policy["allowed_foundational_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("proof foundational axiom policy changed")
    mutation_binding = adoption["mutation_profile"]
    mutation_path = mutation_binding["path"]
    if manifest(root, [mutation_path])[mutation_path] != mutation_binding["sha256"]:
        raise ValueError("semantic calibration profile changed without adoption")
    mutations = json.loads((root / mutation_path).read_text())["mutations"]
    if (len(mutations) != mutation_binding["mutations"]
            or {item["theorem_family"] for item in mutations} != {item["id"] for item in theorems}):
        raise ValueError("semantic calibration coverage differs from required theorem families")
    return {
        "authority": str(relative), "manifest_sha256": digest(manifest_path),
        "members": len(observed), "stages": ids, "gates": gate_ids,
        "required_declarations": declarations,
        "audit_declarations": audited, "audit_policy_sha256": profile_binding["sha256"],
        "source_contract_inputs": source_contract,
        "mutation_profile_sha256": mutation_binding["sha256"],
    }
