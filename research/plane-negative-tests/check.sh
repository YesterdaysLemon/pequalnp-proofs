#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.MetaComplexity.Helpers.PermInputs
scratch=$(mktemp -d)
modules=(KWPartition KWWeight FanoFormula TestCounts SmallAnd TestColoring Plane4Tests Plane4Transport Plane4Posted Plane4Compact)
cleanup() {
    for mod in "${modules[@]}"; do rm -f -- "$scratch/$mod.lean" "$scratch/$mod.olean"; done
    rm -f -- "$scratch/Report.lean"
    rmdir -- "$scratch"
}
trap cleanup EXIT
cp "$src/../G11-formulas/KWPartition.lean" "$scratch/"
for mod in "${modules[@]:1}"; do cp "$src/$mod.lean" "$scratch/"; done
cp "$src/Report.lean" "$scratch/"
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for mod in "$@"; do lean -j1 -o "$mod.olean" "$mod.lean"; done
    lean -j1 Report.lean
' _ "$scratch" "${modules[@]}"
