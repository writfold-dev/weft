"""Behavioral regressions for source closure and attempt-owned cleanup."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import contracts
import evidence
import run_proofs

ROOT = Path(__file__).resolve().parent.parent


class QualificationBoundaries(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="weft-qualification-test-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.source = self.base / "source"
        (self.source / "formal").mkdir(parents=True)
        self.external = self.base / "outside"
        self.external.mkdir()
        (self.external / "Hidden.lean").write_text("namespace Hidden\nend Hidden\n")

    def test_nested_directory_symlink_is_refused(self) -> None:
        (self.source / "formal/linked").symlink_to(self.external, target_is_directory=True)
        with self.assertRaises(ValueError):
            evidence.manifest(self.source, ["formal"])

    def test_root_input_symlink_is_refused(self) -> None:
        (self.source / "linked").symlink_to(self.external, target_is_directory=True)
        with self.assertRaises(ValueError):
            evidence.manifest(self.source, ["linked"])

    def test_explicit_path_through_symlink_is_refused(self) -> None:
        (self.source / "linked").symlink_to(self.external, target_is_directory=True)
        with self.assertRaises(ValueError):
            evidence.manifest(self.source, ["linked/Hidden.lean"])

    def test_parent_escape_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            evidence.manifest(self.source, ["../outside/Hidden.lean"])

    def test_failed_producer_reaps_only_owned_build_tree(self) -> None:
        (self.source / "formal/Probe.lean").write_text("namespace Probe\nend Probe\n")
        output = self.base / "evidence"
        output.mkdir()
        cache = self.base / "cache"
        unrelated = cache / "unrelated"
        unrelated.mkdir(parents=True)
        marker = unrelated / "keep"
        marker.write_text("operator-owned data")
        with (patch.object(run_proofs, "ROOT", self.source),
              patch.object(run_proofs, "EVIDENCE", output),
              patch.object(run_proofs, "CACHE", cache),
              patch.dict(os.environ, {"PATH": ""}),
              contextlib.redirect_stdout(io.StringIO())):
            # Real process lookup fails: no compiler or mocked success is used.
            self.assertEqual(run_proofs.main(), 1)
        self.assertEqual(sorted(path.name for path in cache.iterdir()), ["unrelated"])
        self.assertTrue(marker.is_file())
        self.assertEqual(json.loads((output / "lean-results.json").read_text())["status"], "fail")

    def test_copy_failure_cleans_allocated_owner_directory(self) -> None:
        empty_root = self.base / "missing-formal"
        empty_root.mkdir()
        cache = self.base / "copy-cache"
        with patch.object(run_proofs, "ROOT", empty_root), patch.object(run_proofs, "CACHE", cache):
            with self.assertRaises(FileNotFoundError):
                with run_proofs.clean_copy("copy-failure"):
                    self.fail("copy unexpectedly succeeded")
        self.assertEqual(list(cache.iterdir()), [])

    def copied_contract(self) -> Path:
        destination = self.base / "contract"
        adoption = json.loads((ROOT / "qualification/handover-adoption.json").read_text())
        authorities = [adoption["authority"]] + [
            item["authority"] for item in adoption.get("base_authorities", [])
        ]
        for authority in authorities:
            shutil.copytree(ROOT / authority, destination / authority)
        (destination / "qualification").mkdir(parents=True)
        shutil.copy2(ROOT / "qualification/handover-adoption.json",
                     destination / "qualification/handover-adoption.json")
        related = list(adoption["source_contract_inputs"]) + [
            adoption["proof_profile"]["path"], adoption["mutation_profile"]["path"],
        ]
        for relative in related:
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)
        return destination

    def test_removed_theorem_cannot_redefine_the_audit(self) -> None:
        destination = self.copied_contract()
        contracts.reconcile(destination)
        adoption = json.loads((destination / "qualification/handover-adoption.json").read_text())
        path = destination / adoption["authority"] / "registries/theorems.json"
        registry = json.loads(path.read_text())
        registry["theorems"].pop()
        path.write_text(json.dumps(registry))
        with self.assertRaises(ValueError):
            contracts.reconcile(destination)

    def test_unlisted_contract_member_is_refused(self) -> None:
        destination = self.copied_contract()
        adoption = json.loads((destination / "qualification/handover-adoption.json").read_text())
        (destination / adoption["authority"] / "unlisted.json").write_text("{}\n")
        with self.assertRaises(ValueError):
            contracts.reconcile(destination)

    def inherited_requirements(self) -> tuple[list[Path], list[dict], list[dict]]:
        adoption = json.loads((ROOT / "qualification/handover-adoption.json").read_text())
        authority = ROOT / adoption["authority"]
        bases = [ROOT / item["authority"] for item in adoption.get("base_authorities", [])]
        gates = json.loads((authority / "registries/gates.json").read_text())["stages"]
        theorems = json.loads((authority / "registries/theorems.json").read_text())["theorems"]
        contracts.conserve_requirements(bases, gates, theorems)
        return bases, gates, theorems

    def test_base_theorem_cannot_disappear_in_new_revision(self) -> None:
        bases, gates, theorems = self.inherited_requirements()
        self.assertTrue(bases, "this acceptance profile requires its immutable base")
        shortened = [item for item in theorems if item["id"] != "L12"]
        with self.assertRaises(ValueError):
            contracts.conserve_requirements(bases, gates, shortened)

    def test_base_execution_prerequisites_cannot_be_dropped(self) -> None:
        bases, gates, theorems = self.inherited_requirements()
        for gate in gates:
            if gate["id"] == "P05":
                gate["external_prerequisites"] = []
        with self.assertRaises(ValueError):
            contracts.conserve_requirements(bases, gates, theorems)

    def test_new_stage_cannot_bypass_prior_proof_dependency(self) -> None:
        bases, gates, theorems = self.inherited_requirements()
        for gate in gates:
            if gate["id"] == "P02":
                gate["dependencies"] = []
        with self.assertRaises(ValueError):
            contracts.conserve_requirements(bases, gates, theorems)


if __name__ == "__main__":
    unittest.main()
