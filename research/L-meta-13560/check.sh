#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.BinaryCircuit
modules=(FamilyLive PairedSemantics PairedLower PairedCircuit FullSearch FullProjection SixCofactors CofactorATable CofactorBTable)
scratch=$(mktemp -d)
cleanup() {
    for module in "${modules[@]}"; do rm -f -- "$scratch/$module.lean" "$scratch/$module.olean"; done
    rm -f -- "$scratch/Report.lean" "$scratch/full_basis"
    rmdir -- "$scratch"
}
trap cleanup EXIT
for mod in "${modules[@]}"; do
    if [[ -f "$src/$mod.lean" ]]; then cp "$src/$mod.lean" "$scratch/"; else cp "$src/../L-meta-13719/$mod.lean" "$scratch/"; fi
done
cat > "$scratch/Report.lean" <<'LEAN'
import SixCofactors
import CofactorATable
import CofactorBTable
#print axioms FullSearch.CofactorA.excluded
#print axioms FullSearch.CofactorB.excluded
#print axioms FullSearch.Six.extension_lower
LEAN
lake env bash -euc '
    cd "$1"
    shift
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for module in "$@"; do lean -o "$module.olean" "$module.lean"; done
    lean Report.lean
' _ "$scratch" "${modules[@]}"
python3 "$src/audit.py"
c++ -std=c++20 -O2 "$src/full_basis.cpp" -o "$scratch/full_basis"
"$scratch/full_basis" 5 eee8eec8 6
"$scratch/full_basis" 5 eee8eae0 6
"$scratch/full_basis" 6 eee8eae0eec8eac0 7
