#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.BinaryCircuit PEqualNP.Defs.MetaComplexityLgpMono
scratch=$(mktemp -d)
modules=()
cleanup() {
    for n in "${modules[@]}"; do rm -f -- "$scratch/$n.lean" "$scratch/$n.olean"; done
    rm -f -- "$scratch/Report.lean"
    rmdir -- "$scratch"
}
trap cleanup EXIT
collect() {
    local dir=$1
    shift
    for n in "$@"; do
        modules+=("$n")
        cp "$dir/$n.lean" "$scratch/"
    done
}
collect "$src/../L-meta-13719" FamilyLive PairedSemantics PairedLower PairedCircuit PairedUpper PairedExact
collect "$src/../read-once-inputs" ReadOnceSplit SplitCircuits SplitMonotone PairedExpansion
collect "$src/../L-meta-13560" FullSearch FullProjection
collect "$src/../induced-small-graphs" EssentialRestrictions CycleTable CycleCircuit InducedCycle CycleExpansions
collect "$src" BinarySubstitution BinaryWireCost ReadOnceBinary
cp "$src/Report.lean" "$scratch/"
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for n in "$@"; do lean -o "$n.olean" "$n.lean"; done
    lean Report.lean
' _ "$scratch" "${modules[@]}"
