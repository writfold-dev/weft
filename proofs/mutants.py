#!/usr/bin/env python3
"""Mutant calibration for the `proofs` gate.

Every proved kernel function gets at least one semantic mutation of its Rust
source. For each: copy the crate, apply the mutation, translate it exactly as
the gate does (proofs/extract.sh), build the theorems against the mutated
translation in a scratch copy of the lake project, and require the build to
FAIL inside the named theorem(s) — no other theorem may fail, and the
translation itself must still type-check. A proof that survives its mutant
proves nothing; a failure anywhere else is noise, not calibration.
"""
from dataclasses import dataclass
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PROOFS = ROOT / "proofs"
KERNEL = ROOT / "crates" / "weft-core"


@dataclass(frozen=True)
class Mutant:
    name: str
    file: str
    before: str
    after: str
    fails: tuple[str, ...]


MUTANTS = (
    # sets: the first position, not any later one, answers position_of
    Mutant("position-of-first-only", "sets.rs",
           "        if values[i] == value {\n            return Some(i);",
           "        if values[i] == value {\n            return Some(0);",
           ("Weft.Core.position_of_loop_spec",)),
    # sets (A01 normalization): a duplicate occurrence never becomes a second member
    Mutant("normalize-keeps-duplicates", "sets.rs",
           "        if !contains(&extended, raw[i]) {\n            extended.push(raw[i]);\n        }",
           "        extended.push(raw[i]);",
           ("Weft.Core.extend_unique_loop_spec",)),
    # sets (A01 display order): union is left order first, never right-first
    Mutant("union-right-first", "sets.rs",
           "    extend_unique(normalize(left), right)",
           "    extend_unique(normalize(right), left)",
           ("Weft.Core.union_spec",)),
    # sets (A01): intersection keeps exactly the left values present on the right
    Mutant("intersection-as-difference", "sets.rs",
           "    select(left, right, true)",
           "    select(left, right, false)",
           ("Weft.Core.intersection_spec",)),
    # sets (A01): difference never keeps a removed value
    Mutant("difference-keeps-removed", "sets.rs",
           "    select(left, right, false)",
           "    select(left, right, true)",
           ("Weft.Core.difference_spec",)),
    # sets: the shared filter decides by the requested polarity
    Mutant("select-inverted", "sets.rs",
           "        if contains(right, left[i]) == present {",
           "        if contains(right, left[i]) != present {",
           ("Weft.Core.select_loop_spec",)),
    # sets (A03): subset inspects every left member, including the last
    Mutant("subset-skips-last", "sets.rs",
           "    while i < left.len() {\n        if !contains(right, left[i]) {",
           "    while i + 1 < left.len() {\n        if !contains(right, left[i]) {",
           ("Weft.Core.subset_loop_spec",)),
    # sets: extensional equality needs both inclusions
    Mutant("same-members-one-way", "sets.rs",
           "subset(left, right).is_none() && subset(right, left).is_none()",
           "subset(left, right).is_none() && subset(left, right).is_none()",
           ("Weft.Core.same_members_spec",)),
    # verdict: a row whose premises fail contributes nothing
    Mutant("role-ignores-premises", "verdict.rs",
           "    if !row.premises_hold {",
           "    if !row.premises_hold && !row.query {",
           ("Weft.Core.role_spec",)),
    # verdict: no premise model is inconsistent, never vacuously entailed
    Mutant("verdict-vacuous-entailment", "verdict.rs",
           "    } else {\n        LogicalVerdict::InconsistentPremises\n    }",
           "    } else {\n        LogicalVerdict::Entailed\n    }",
           ("Weft.Core.verdict_of_spec",)),
    # verdict: a refuting model is never recorded as support
    Mutant("classify-refuting-as-support", "verdict.rs",
           "            RowRole::Refuting => refuting = true,",
           "            RowRole::Refuting => supporting = true,",
           # `refuting` is then never assigned, so it leaves the loop state and
           # the loop's signature: the top-level proof breaks too
           ("Weft.Core.classify_loop_spec", "Weft.Core.classify_spec")),
    # scope: byte equality includes the length
    Mutant("same-bytes-ignores-length", "scope.rs",
           "    if left.len() != right.len() {\n        return false;\n    }\n",
           "",
           ("Weft.Core.same_bytes_spec",)),
    # scope: byte equality compares the last byte too
    Mutant("same-bytes-prefix", "scope.rs",
           "    while i < left.len() {\n        if left[i] != right[i] {",
           "    while i + 1 < left.len() {\n        if left[i] != right[i] {",
           ("Weft.Core.same_bytes_loop_spec",)),
    # scope: a diagnostics-only report kind is refused, not required
    Mutant("unequal-requirement-as-equal", "scope.rs",
           "        Requirement::Unequal => !equal,",
           "        Requirement::Unequal => equal,",
           ("Weft.Core.satisfied_spec",)),
    # scope: the first comparison (the source digest) is never skipped
    Mutant("refusals-skip-first", "scope.rs",
           "        if !satisfied(&comparisons[i]) {",
           "        if !satisfied(&comparisons[i]) && i > 0 {",
           ("Weft.Core.refusals_loop_spec",)),
)

# lake reports `error: <path>.lean:<line>:<col>: <message>`
ERROR = re.compile(r"^error:\s*(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):", re.M)
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[^\s:(]+)", re.M)
NAMESPACE = re.compile(r"^namespace\s+(?P<name>\S+)", re.M)


def declarations(path: Path) -> list[tuple[int, str]]:
    """(line, fully qualified name) of every declaration in a theorem file."""
    namespace = ""
    found = []
    for number, line in enumerate(path.read_text().splitlines(), start=1):
        if match := NAMESPACE.match(line):
            namespace = match.group("name") + "."
            continue
        if line.startswith("end "):
            namespace = ""
            continue
        if match := DECLARATION.match(line):
            found.append((number, namespace + match.group("name")))
    return found


def attribute(file: Path, line: int) -> str | None:
    enclosing = None
    for start, name in declarations(file):
        if start <= line:
            enclosing = name
    return enclosing


def failing_theorems(output: str, project: Path) -> tuple[set[str], list[str]]:
    failures: set[str] = set()
    unattributed: list[str] = []
    for match in ERROR.finditer(output):
        file = (project / match.group("file")).resolve()
        try:
            relative = file.relative_to(project)
        except ValueError:
            unattributed.append(match.group(0))
            continue
        if relative.parts[0] != "Kernel" or not file.exists():
            unattributed.append(str(relative))
            continue
        name = attribute(file, int(match.group("line")))
        if name is None:
            unattributed.append(str(relative))
        else:
            failures.add(name)
    return failures, unattributed


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, timeout=1800)


def calibrate(mutant: Mutant, scratch: Path) -> None:
    crate = scratch / "crate"
    shutil.copytree(KERNEL, crate, ignore=shutil.ignore_patterns("target"))
    source = crate / "src" / mutant.file
    text = source.read_text()
    if text.count(mutant.before) != 1:
        raise SystemExit(f"FAIL {mutant.name}: mutation site does not match exactly once")
    source.write_text(text.replace(mutant.before, mutant.after))

    extraction = run(["sh", str(PROOFS / "extract.sh"), str(crate), str(scratch / "Extracted")], ROOT)
    if extraction.returncode != 0:
        print(extraction.stdout)
        raise SystemExit(f"FAIL {mutant.name}: the mutated kernel did not translate")

    project = scratch / "proofs"
    project.mkdir()
    for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "Kernel.lean", "Audit.lean"):
        shutil.copy2(PROOFS / name, project / name)
    shutil.copytree(PROOFS / "Kernel", project / "Kernel")
    shutil.copytree(scratch / "Extracted", project / "Extracted")
    (project / ".lake").mkdir()
    os.symlink(PROOFS / ".lake" / "packages", project / ".lake" / "packages")

    build = run(["lake", "build"], project)
    if build.returncode == 0:
        raise SystemExit(f"FAIL {mutant.name}: the proofs still build against the mutated kernel")
    failures, unattributed = failing_theorems(build.stdout, project)
    if unattributed:
        print(build.stdout)
        raise SystemExit(f"FAIL {mutant.name}: errors outside the theorem files: {unattributed}")
    expected = set(mutant.fails)
    if not failures or not expected <= failures:
        print(build.stdout)
        print(f"attributed failures: {sorted(failures)}")
        raise SystemExit(f"FAIL {mutant.name}: expected {sorted(expected)} to fail, got {sorted(failures)}")
    if failures - expected:
        print(build.stdout)
        raise SystemExit(f"FAIL {mutant.name}: unexpected failing theorems {sorted(failures - expected)}")
    print(f"calibration: {mutant.name} rejected by {', '.join(sorted(failures))}", flush=True)


def main() -> None:
    selected = set(sys.argv[1:])
    mutants = [m for m in MUTANTS if not selected or m.name in selected]
    if selected and len(mutants) != len(selected):
        raise SystemExit(f"unknown mutant(s): {sorted(selected - {m.name for m in mutants})}")
    # Every mutant runs even after a failure, so one gate run reports them all.
    failed: list[str] = []
    for mutant in mutants:
        with tempfile.TemporaryDirectory(prefix=f"mutant-{mutant.name}-") as directory:
            try:
                calibrate(mutant, Path(directory))
            except SystemExit as error:
                print(error, flush=True)
                failed.append(mutant.name)
    if failed:
        raise SystemExit(f"FAIL: {len(failed)} mutant(s) not calibrated: {failed}")
    print(f"PROOF_CALIBRATIONS={len(mutants)}", flush=True)


if __name__ == "__main__":
    main()
