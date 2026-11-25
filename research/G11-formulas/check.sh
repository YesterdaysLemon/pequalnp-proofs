#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Defs.EdgeOwnership
scratch=$(mktemp -d)
modules=(KWPartition KWEncoding KWSemantics G11Game G11Upper G11Bridge G11Project)
cleanup() {
    for name in "${modules[@]}"; do rm -f -- "$scratch/$name.lean" "$scratch/$name.olean"; done
    rm -f -- "$scratch/formula.lrat" "$scratch/formula.cnf" "$scratch/Report.lean"
    rmdir -- "$scratch"
}
trap cleanup EXIT
for name in "${modules[@]}"; do cp "$src/$name.lean" "$scratch/"; done
cp "$src/Report.lean" "$scratch/"
gzip -dc "$src/formula-22.lrat.gz" > "$scratch/formula.lrat"
lake env bash -euc '
    cd "$1"
    regenerate=$2
    shift 2
    export LEAN_PATH="$PWD:$LEAN_PATH"
    for name in "$@"; do lean -o "$name.olean" "$name.lean"; done
    lean --run G11Game.lean check formula.lrat
    if [[ "$regenerate" == --regenerate ]]; then
        lean --run G11Game.lean write formula.cnf
        rc=0
        "$(lean --print-prefix)/bin/cadical" --quiet --lrat --no-binary formula.cnf formula.lrat || rc=$?
        [[ $rc == 20 ]]
        lean --run G11Game.lean check formula.lrat
    fi
    lean Report.lean
' _ "$scratch" "${1:-}" "${modules[@]}"
