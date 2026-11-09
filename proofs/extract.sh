#!/bin/sh
# Translate the kernel crate to Lean: Charon (Rust → LLBC) then Aeneas
# (LLBC → Lean), exactly as the `proofs` gate and the mutant calibration do.
#
#   sh proofs/extract.sh <kernel-crate-dir> <dest-dir>
#
# The crate is copied into a throwaway shadow workspace that carries the
# real root's `[workspace.package]` values the kernel inherits and nothing
# else, so Charon never loads the full workspace and every run sees the same
# relative paths (crates/weft-core/src/...), which Aeneas records in its output.
set -eu
crate="$(cd "$1" && pwd)"
dest="$2"
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

python3 - "$root/Cargo.toml" "$crate/Cargo.toml" "$work/Cargo.toml" <<'PY'
import json, sys, tomllib
root, kernel, out = sys.argv[1], sys.argv[2], sys.argv[3]
with open(root, "rb") as handle:
    package = tomllib.load(handle)["workspace"]["package"]
with open(kernel, "rb") as handle:
    inherited = [key for key, value in tomllib.load(handle)["package"].items()
                 if isinstance(value, dict) and value.get("workspace")]
lines = ['[workspace]', 'members = ["crates/weft-core"]', 'resolver = "3"', '', '[workspace.package]']
lines += [f'{key} = {json.dumps(package[key])}' for key in inherited]
open(out, "w").write("\n".join(lines) + "\n")
PY
mkdir -p "$work/crates"
cp -R "$crate" "$work/crates/weft-core"
rm -rf "$work/crates/weft-core/target"

cd "$work/crates/weft-core"
# --preset=aeneas is the option set Aeneas's own test-suite drives Charon
# with; the rest of the configuration is [package.metadata.charon].
charon cargo --preset=aeneas --dest-file "$work/weft_core.llbc" -- --lib

rm -rf "$dest"
mkdir -p "$dest"
aeneas -backend lean -no-progress-bar -abort-on-error -dest "$dest" "$work/weft_core.llbc"
echo "extracted: $(ls "$dest" | tr '\n' ' ')"
