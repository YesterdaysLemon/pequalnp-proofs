#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$src/../.." && pwd -P)
case "${1:-}" in
    or|mixed) mode=$1 ;;
    *) echo "Usage: bash check-shared.sh or|mixed [--quick]" >&2; exit 2 ;;
esac
scratch=$(mktemp -d)
cleanup() {
    rm -f -- "$scratch/CheckDimacs.lean" "$scratch/check.c" "$scratch/check" "$scratch/result.json" "$scratch/result.tmp" "$scratch/prefix.json"
    rmdir -- "$scratch"
}
trap cleanup EXIT
cp "$src/CheckDimacs.lean" "$scratch/"
cd "$repo/lean"
lake env bash -euc '
    cd "$1"
    lean -c check.c CheckDimacs.lean
    leanc -O2 -o check check.c
    args=()
    if [[ "$3" == mixed ]]; then
        python3 "$2/g11-prefix.py" prefix.json --max 4
        args+=(--mixed "$PWD/prefix.json")
    fi
    if [[ "$4" == --quick ]]; then args+=(--limit 1); fi
    python3 "$2/certify-g11.py" "$(lean --print-prefix)/bin/cadical" "$PWD/check" "$PWD/result.json" "${args[@]}"
    python3 "$2/compare-results.py" "$3" "$PWD/result.json" "$4"
' _ "$scratch" "$src" "$mode" "${2:-}"
