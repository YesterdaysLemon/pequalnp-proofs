#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd -P)
repo=$(cd "$source_dir/../.." && pwd -P)
cd "$repo/lean"
lake build PEqualNP.Outside.L_meta_12072
scratch=$(mktemp -d)
trap 'rm -f -- "$scratch/BlockFamily.lean" "$scratch/Sibling12074.lean" "$scratch/BlockFamily.olean"; rmdir -- "$scratch"' EXIT
cp "$source_dir/BlockFamily.lean" "$source_dir/Sibling12074.lean" "$scratch/"
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:$LEAN_PATH"
  lean -o BlockFamily.olean BlockFamily.lean
  lean Sibling12074.lean
' _ "$scratch"
