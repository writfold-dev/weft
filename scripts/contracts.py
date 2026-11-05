"""Reconcile immutable requirements and inherited obligations before qualification."""
from __future__ import annotations

import json
from pathlib import Path
import re

from evidence import digest, manifest


def checked_contract(root: Path, relative: Path, pinned: str) -> tuple[Path, dict[str, str]]:
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("handover authority must remain inside the source root")
    authority = root / relative
    manifest(root, [str(relative / "MANIFEST.sha256")])
    manifest_path = authority / "MANIFEST.sha256"
    if digest(manifest_path) != pinned:
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
    return authority, observed


def inherited_contracts(root: Path, authority: Path, adoption: dict) -> list[Path]:
    pins = {item["authority"]: item["manifest_sha256"]
            for item in adoption.get("base_authorities", [])}
    if len(pins) != len(adoption.get("base_authorities", [])):
        raise ValueError("duplicate inherited authority")
    used: set[str] = set()
    bases = []
    current = authority
    while (current / "base.json").is_file():
        parent = json.loads((current / "base.json").read_text())
        name = parent["authority"]
        if name in used or name == adoption["authority"] or pins.get(name) != parent["manifest_sha256"]:
            raise ValueError("missing, cyclic or changed inherited authority")
        current, _ = checked_contract(root, Path(name), pins[name])
        used.add(name)
        bases.append(current)
    if used != set(pins):
        raise ValueError("unreferenced inherited authority in adoption")
    return bases


def conserve_requirements(bases: list[Path], gates: list[dict], theorems: list[dict]) -> None:
    current_gates = {item["id"]: item for item in gates}
    current_theorems = {item["id"]: item for item in theorems}
    ancestors: dict[str, set[str]] = {}
    for gate in gates:
        ancestors[gate["id"]] = set(gate["dependencies"]).union(
            *(ancestors[dependency] for dependency in gate["dependencies"])
        )
    for base in bases:
        for old in json.loads((base / "registries/theorems.json").read_text())["theorems"]:
            current = current_theorems.get(old["id"], {})
            if any(current.get(key) != value for key, value in old.items()):
                raise ValueError("an inherited theorem obligation was removed or weakened")
        for old in json.loads((base / "registries/gates.json").read_text())["stages"]:
            current = current_gates.get(old["id"])
            if (current is None or current["gate"] != old["gate"] or current["required"] is not True
                    or not set(old["dependencies"]) <= ancestors[old["id"]]
                    or not set(old["external_prerequisites"]) <= set(current["external_prerequisites"])):
                raise ValueError("an inherited stage/gate dependency was removed or weakened")


def reconcile(root: Path) -> dict[str, object]:
    adoption = json.loads((root / "qualification/handover-adoption.json").read_text())
    relative = Path(adoption["authority"])
    authority, observed = checked_contract(root, relative, adoption["manifest_sha256"])
    bases = inherited_contracts(root, authority, adoption)
    gates = json.loads((authority / "registries/gates.json").read_text())["stages"]
    theorems = json.loads((authority / "registries/theorems.json").read_text())["theorems"]
    inventory = adoption["inventory"]
    ids = [entry["id"] for entry in gates]
    gate_ids = [entry["gate"] for entry in gates]
    primary_declarations = [entry["declaration"] for entry in theorems]
    declarations = list(dict.fromkeys(
        name for entry in theorems
        for name in [entry["declaration"], *entry.get("supporting_declarations", [])]
    ))
    theorem_ids = [entry["id"] for entry in theorems]
    if (len(ids) != inventory["stages"] or len(set(ids)) != len(ids)
            or len(gate_ids) != inventory["gates"] or len(set(gate_ids)) != len(gate_ids)
            or len(primary_declarations) != inventory["language_theorems"]
            or len(set(primary_declarations)) != len(primary_declarations)
            or len(set(theorem_ids)) != len(theorem_ids)):
        raise ValueError("stage/gate/theorem inventory differs from adoption")
    seen = set()
    for stage in gates:
        if stage["required"] is not True or not set(stage["dependencies"]) <= seen:
            raise ValueError("invalid required stage or dependency order")
        seen.add(stage["id"])
    if any(theorem["required"] is not True for theorem in theorems):
        raise ValueError("required language theorem was weakened")
    conserve_requirements(bases, gates, theorems)
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
    if (len(extra) != profile_binding["additional_declarations"] or len(set(audited)) != len(audited)
            or any(not re.fullmatch(r"Weft\.[A-Za-z0-9_.]+", name) for name in audited)):
        raise ValueError("expanded proof declaration inventory is invalid")
    if set(policy["allowed_foundational_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("proof foundational axiom policy changed")
    mutation_binding = adoption["mutation_profile"]
    mutation_path = mutation_binding["path"]
    if manifest(root, [mutation_path])[mutation_path] != mutation_binding["sha256"]:
        raise ValueError("semantic calibration profile changed without adoption")
    mutations = json.loads((root / mutation_path).read_text())["mutations"]
    if len(mutations) != mutation_binding["mutations"] or {item["theorem_family"] for item in mutations} != set(theorem_ids):
        raise ValueError("semantic calibration coverage differs from required theorem families")
    return {
        "authority": str(relative), "manifest_sha256": adoption["manifest_sha256"],
        "base_authorities": [str(base.relative_to(root)) for base in bases],
        "members": len(observed), "stages": ids, "gates": gate_ids,
        "required_declarations": declarations, "theorem_ids": theorem_ids,
        "audit_declarations": audited, "audit_policy_sha256": profile_binding["sha256"],
        "source_contract_inputs": source_contract,
        "mutation_profile_sha256": mutation_binding["sha256"],
    }
