#!/usr/bin/env bash
set -euo pipefail
notes_dir="$(cd "$(dirname "$0")" && pwd)"
build_dir="$(mktemp -d)"
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir:${LEAN_PATH:-}"
cd "$notes_dir"
lean --version
for module in Transfer FixedPoints OrderReflection BlockBound CollatzResearch ResidualStateBound HenriquesCore IndexBound; do
  lean -o "$build_dir/$module.olean" "$module.lean"
done
