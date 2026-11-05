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
        source = ROOT / "handovers/revision-1/weft"
        shutil.copytree(source, destination / "handovers/revision-1/weft")
        (destination / "qualification").mkdir()
        shutil.copy2(ROOT / "qualification/handover-adoption.json",
                     destination / "qualification/handover-adoption.json")
        adoption = json.loads((ROOT / "qualification/handover-adoption.json").read_text())
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
        path = destination / "handovers/revision-1/weft/registries/theorems.json"
        registry = json.loads(path.read_text())
        registry["theorems"].pop()
        path.write_text(json.dumps(registry))
        with self.assertRaises(ValueError):
            contracts.reconcile(destination)

    def test_unlisted_contract_member_is_refused(self) -> None:
        destination = self.copied_contract()
        (destination / "handovers/revision-1/weft/unlisted.json").write_text("{}\n")
        with self.assertRaises(ValueError):
            contracts.reconcile(destination)


if __name__ == "__main__":
    unittest.main()
