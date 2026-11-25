#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$source_dir/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.BinaryCircuit PEqualNP.Defs.MetaComplexityLgpMono
scratch=$(mktemp -d)
modules=(FamilyLive PairedSemantics PairedLower PairedCircuit PairedUpper PairedExact)
cleanup() {
    for module in "${modules[@]}"; do
        rm -f -- "$scratch/$module.lean" "$scratch/$module.olean"
    done
    rm -f -- "$scratch/Assumptions.lean"
    rmdir -- "$scratch"
}
trap cleanup EXIT
for module in "${modules[@]}"; do
    cp "$source_dir/$module.lean" "$scratch/"
done
cp "$source_dir/Assumptions.lean" "$scratch/"
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for module in "$@"; do
        lean -o "$module.olean" "$module.lean"
    done
    lean Assumptions.lean
' _ "$scratch" "${modules[@]}"
python3 "$source_dir/audit.py"
