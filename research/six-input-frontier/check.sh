#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
scratch=$(mktemp -d)
trap 'rm -f -- "$scratch/search" "$scratch/orbits"; rmdir -- "$scratch"' EXIT
export PYTHONDONTWRITEBYTECODE=1
"${CXX:-c++}" -O3 -std=c++20 "$src/../five-input-circuits/bounded-circuits.cpp" -o "$scratch/search"
"${CXX:-c++}" -O3 -std=c++20 "$src/orbits.cpp" -o "$scratch/orbits"
python3 "$src/../five-input-circuits/catalogue.py" "$src/../five-input-circuits/circuits.json" --binary "$scratch/search"
python3 "$src/replay.py" "$scratch/search" "$scratch/orbits"
