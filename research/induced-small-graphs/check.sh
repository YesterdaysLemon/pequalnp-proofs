#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.BinaryCircuit PEqualNP.Defs.MetaComplexityLgpMono
base_modules=(FamilyLive PairedSemantics PairedLower PairedCircuit PairedUpper PairedExact)
splits=(ReadOnceSplit SplitCircuits SplitMonotone)
search=(FullSearch FullProjection)
local_modules=(EssentialRestrictions CycleTable CycleCircuit InducedCycle CycleExpansions)
modules=("${base_modules[@]}" "${splits[@]}" "${search[@]}" "${local_modules[@]}")
scratch=$(mktemp -d)
cleanup() {
    for name in "${modules[@]}"; do rm -f -- "$scratch/$name.lean" "$scratch/$name.olean"; done
    for n in 2 3 4 5; do rm -f -- "$scratch/graph-$n.json"; done
    rm -f -- "$scratch/Report.lean" "$scratch/small-graphs"
    rmdir -- "$scratch"
}
trap cleanup EXIT
for n in "${base_modules[@]}"; do cp "$src/../L-meta-13719/$n.lean" "$scratch/"; done
for n in "${splits[@]}"; do cp "$src/../read-once-inputs/$n.lean" "$scratch/"; done
for n in "${search[@]}"; do cp "$src/../L-meta-13560/$n.lean" "$scratch/"; done
for n in "${local_modules[@]}"; do cp "$src/$n.lean" "$scratch/"; done
cp "$src/Report.lean" "$scratch/"
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for n in "$@"; do lean -o "$n.olean" "$n.lean"; done
    lean Report.lean
' _ "$scratch" "${modules[@]}"
"${CXX:-c++}" -std=c++20 -O2 "$src/small_graph.cpp" -o "$scratch/small-graphs"
for n in 2 3 4 5; do
    python3 "$src/small-graphs.py" "$scratch/small-graphs" "$scratch/graph-$n.json" --size "$n" --cap 30000000
    cmp "$scratch/graph-$n.json" "$src/graph-$n.json"
done
