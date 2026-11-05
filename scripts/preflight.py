"""Observe the operator's existing storage policy; never replace its binding."""
from __future__ import annotations

import importlib
import json
import os
from pathlib import Path
import subprocess
import sys


def observe(root: Path) -> dict[str, object]:
    infra = Path(os.environ.get("WEFT_CI_INFRA", str(root.parent / "ci-infra"))).resolve()
    state = Path(os.environ.get(
        "WEFT_CI_STATE", str(Path.home() / ".local/share/buildbot-ci"),
    )).resolve()
    if not (infra / "ci_infra/storage.py").is_file():
        raise ValueError("set WEFT_CI_INFRA to the operator's installed ci-infra checkout")
    if not (state / "storage.json").is_file():
        raise ValueError("missing operator storage binding; no fallback is permitted")
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(infra))
    storage = importlib.import_module("ci_infra.storage").check(state)
    if storage is None:
        raise ValueError("storage observation did not admit the configured binding")
    capacity = json.loads(subprocess.check_output([
        "docker", "info", "--format",
        '{"cpus":{{.NCPU}},"memory_bytes":{{.MemTotal}}}',
    ], text=True, timeout=30))
    if capacity["cpus"] < 8 or capacity["memory_bytes"] < 12884901888:
        raise ValueError("Docker capacity is below the existing admitted resource bound")
    return {"storage": storage, "capacity": capacity}
