#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd -P)
scratch=$(mktemp -d)
trap 'rm -f -- "$scratch/search"; rmdir -- "$scratch"' EXIT
"${CXX:-c++}" -O3 -std=c++20 "$src/bounded-circuits.cpp" -o "$scratch/search"
python3 "$src/catalogue.py" "$src/circuits.json" --binary "$scratch/search"
