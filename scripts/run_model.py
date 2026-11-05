"""Run TLC on the control-protocol seed and every mutant, then TLAPS proofs."""
from __future__ import annotations

import json
import re
import shutil
import tempfile
from pathlib import Path

from evidence import manifest, require_success, run_logged, write_new

ROOT = Path("/work/weft")
EVIDENCE = Path("/evidence")
TLC = ["java", "-XX:+UseParallelGC", "-cp", "/opt/tla/tla2tools.jar", "tlc2.TLC"]
TLAPM = "/opt/tlapm/bin/tlapm"
TOOLS = [
    ["java", "-version"],
    [TLAPM, "--version"],
    ["sha256sum", "/opt/tla/tla2tools.jar", TLAPM],
]


def base_check(model: Path) -> dict[str, object]:
    record = run_logged(
        TLC + ["-config", "Control.cfg", "Control.tla"], model, EVIDENCE,
        "tlc-control", timeout=300,
    )
    require_success(record)
    output = (EVIDENCE / "tlc-control.stdout").read_text()
    if "is violated" in output or "Error:" in output:
        raise ValueError("TLC reported a violation or error for the base seed")
    counts = re.search(r"(\d+) states generated, (\d+) distinct states found", output)
    if counts is None or counts.group(2) == "0":
        raise ValueError("TLC did not explore any distinct state")
    return {
        "record": record, "states_generated": int(counts.group(1)),
        "distinct_states": int(counts.group(2)),
    }


def mutant_checks(model: Path, mutants: list[dict]) -> list[dict]:
    results = []
    for spec in mutants:
        module = Path(spec["module"]).stem
        directory = model / Path(spec["module"]).parent
        config = directory / f"{module}.cfg"
        label = f"tlc-{module.lower()}"
        config.write_text(
            f"SPECIFICATION Spec\n"
            f"INVARIANT {spec['target_invariant']}\nCHECK_DEADLOCK FALSE\n"
        )
        record = run_logged(
            TLC + ["-config", config.name, f"{module}.tla"], directory, EVIDENCE,
            label, timeout=300,
        )
        output = (EVIDENCE / f"{label}.stdout").read_text()
        violated = f"Invariant {spec['target_invariant']} is violated" in output
        trace = re.search(r"Error: Invariant .* is violated.*", output) is not None
        if record["exit_code"] == 0 or not violated or not trace:
            raise ValueError(
                f"mutant {spec['name']} did not violate {spec['target_invariant']} "
                f"with a retained counterexample trace",
            )
        results.append({
            "name": spec["name"], "target_invariant": spec["target_invariant"],
            "violated": True, "record": record,
        })
    return results


def proofs(model: Path) -> dict[str, object]:
    record = run_logged(
        [TLAPM, "ControlSafety.tla"], model, EVIDENCE, "tlapm-controlsafety",
        timeout=1200,
    )
    require_success(record)
    output = "\n".join([
        (EVIDENCE / "tlapm-controlsafety.stdout").read_text(),
        (EVIDENCE / "tlapm-controlsafety.stderr").read_text(),
    ])
    if "obligations failed" in output or "backend errors" in output:
        raise ValueError("tlapm reported failed obligations")
    proved = (re.search(r"All (\d+) obligations proved", output)
              or re.search(r"(\d+)/(\d+) obligations proved", output))
    if proved is None:
        raise ValueError("tlapm did not report a complete proof summary")
    numbers = proved.groups()
    if len(numbers) == 2 and numbers[0] != numbers[1]:
        raise ValueError("tlapm did not prove every obligation")
    return {"record": record, "obligations": int(numbers[-1])}


def main() -> int:
    result: dict = {
        "schema_version": 1, "status": "fail",
        "scope": "weft-writfold-control-protocol-model-only", "skipped": [],
    }
    try:
        inputs = manifest(ROOT, ["model"])
        for index, tool in enumerate(TOOLS):
            require_success(run_logged(tool, ROOT, EVIDENCE, f"tool-{index}"))
        with tempfile.TemporaryDirectory(prefix="weft-model-") as owned:
            model = Path(owned) / "model"
            shutil.copytree(ROOT / "model", model)
            result["tlc"] = base_check(model)
            mutants = json.loads((ROOT / "model/mutants.json").read_text())["mutants"]
            result["mutants"] = mutant_checks(model, mutants)
            result["tlaps"] = proofs(model)
        if inputs != manifest(ROOT, ["model"]):
            raise ValueError("model inputs changed during qualification")
        result["inputs"] = inputs
        result["status"] = "pass"
    except (OSError, ValueError, KeyError) as error:
        result["error"] = f"{type(error).__name__}: {error}"
    write_new(EVIDENCE / "model-results.json", result)
    print(json.dumps({
        "status": result["status"],
        "distinct_states": result.get("tlc", {}).get("distinct_states"),
        "mutants_violated": len(result.get("mutants", [])),
        "obligations": result.get("tlaps", {}).get("obligations"),
    }, indent=2), flush=True)
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
