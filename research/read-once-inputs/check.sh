#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$here/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.BinaryCircuit PEqualNP.Defs.MetaComplexityLgpMono
scratch=$(mktemp -d)
base_modules=(FamilyLive PairedSemantics PairedLower PairedCircuit PairedUpper PairedExact)
split_modules=(ReadOnceSplit SplitCircuits SplitMonotone PairedExpansion)
modules=("${base_modules[@]}" "${split_modules[@]}")
cleanup() {
    for module in "${modules[@]}"; do
        rm -f -- "$scratch/$module.lean" "$scratch/$module.olean"
    done
    rm -f -- "$scratch/Assumptions.lean"
    rmdir -- "$scratch"
}
trap cleanup EXIT
for module in "${base_modules[@]}"; do
    cp "$here/../L-meta-13719/$module.lean" "$scratch/"
done
for module in "${split_modules[@]}"; do
    cp "$here/$module.lean" "$scratch/"
done
cp "$here/Assumptions.lean" "$scratch/"
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for module in "$@"; do
        lean -o "$module.olean" "$module.lean"
    done
    lean Assumptions.lean
' _ "$scratch" "${modules[@]}"
