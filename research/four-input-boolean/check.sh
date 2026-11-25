#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
scratch=$(mktemp -d)
trap 'rm -f -- "$scratch/search" "$scratch/circuits.json" "$scratch/circuits.tmp"; rmdir -- "$scratch"' EXIT
export PYTHONDONTWRITEBYTECODE=1
"${CXX:-c++}" -O3 -std=c++20 "$src/../five-input-circuits/bounded-circuits.cpp" -o "$scratch/search"
python3 "$src/enumerate.py" "$scratch/search" "$scratch/circuits.json" --cap 12000000 --compare "$src/circuits.json"
