#!/usr/bin/env bash
set -euo pipefail

# Install Elan and prepare the dependencies recorded in the registry:
#   git clone https://github.com/google-deepmind/formal-conjectures.git
#   git -C formal-conjectures checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
#   (cd formal-conjectures && lake exe cache get)
# Usage: bash verify-slices.sh /path/to/formal-conjectures /path/to/mo-184507.lean

src=$(cd -- "$(dirname -- "$0")" && pwd)
project=$(cd -- "${1:?Pass the formal-conjectures checkout path}" && pwd)
statement=${2:?Pass the path to the registered statement file}
pin=9097e2f90e66d2f6244209cb1c07f7120d17ec53
if [[ $(git -C "$project" rev-parse HEAD) != "$pin" ]]; then
  echo "Expected formal-conjectures revision $pin" >&2
  exit 1
fi

build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
mkdir "$build/OMAStatements"
cp "$statement" "$build/OMAStatements/S_mo_184507.lean"
cp "$src/SliceBounds.lean" "$build"
cd "$project"
lake env bash -s "$build" <<'BUILD'
set -euo pipefail
build=$1
export LEAN_PATH="$build:$LEAN_PATH"
cd "$build"
lean --version
lean -o OMAStatements/S_mo_184507.olean OMAStatements/S_mo_184507.lean
lean SliceBounds.lean | tee Results.log
for decl in continuousOn_sliceLength one_le_sliceLength disproof_of_prescription; do
  grep -Fxq "'SliceBounds.$decl' depends on axioms: [propext, Classical.choice, Quot.sound]" Results.log
done
BUILD
