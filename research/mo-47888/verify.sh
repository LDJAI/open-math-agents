#!/usr/bin/env bash
set -euo pipefail

# Prerequisites: Git, Elan (Lean's toolchain manager), Bash, and the mathlib cache.
# One-time setup:
#   git clone https://github.com/google-deepmind/formal-conjectures.git
#   git -C formal-conjectures checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
#   (cd formal-conjectures && lake exe cache get)
# Run this script from any directory:
#   bash /path/to/verify.sh /path/to/formal-conjectures
# The pinned manifest selects Lean 4.33.1 and mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
# Compilation uses fresh temporary output. The conjecture statement deliberately
# contains a placeholder. The theorems audited below must be independent of it.

sources=$(cd -- "$(dirname -- "$0")" && pwd)
project=$(cd -- "${1:?Pass the path to the pinned formal-conjectures checkout}" && pwd)
expected_commit=9097e2f90e66d2f6244209cb1c07f7120d17ec53
if [[ $(git -C "$project" rev-parse HEAD) != "$expected_commit" ]]; then
    echo "Expected formal-conjectures commit $expected_commit" >&2
    exit 1
fi

build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
mkdir -p "$build/OMAStatements" "$build/OMAProofs"
cp "$sources/Statement.lean" "$build/OMAStatements/S_mo_47888.lean"
cp "$sources/Disproof.lean" "$build/OMAProofs/Multinomial.lean"
cp "$sources/Binary.lean" "$sources/Classification.lean" "$sources/Routing.lean" "$build"
cat > "$build/Audit.lean" <<'LEAN'
import Classification
import Routing
#print axioms OMA.disproof
#print axioms OMA.MultinomialWitness.monotonicity_fails_every_trial_count
#print axioms MultinomialClassification.classification
#print axioms MultinomialRouting.average_load
#print axioms MultinomialRouting.link_cost_monotone
#print axioms MultinomialRouting.routing_monotone
LEAN

cd "$project"
lake env bash -s "$build" <<'BUILD'
set -euo pipefail
build=$1
export LEAN_PATH="$build:$LEAN_PATH"
cd "$build"
lean --version
lean -o OMAStatements/S_mo_47888.olean OMAStatements/S_mo_47888.lean
lean -o OMAProofs/Multinomial.olean OMAProofs/Multinomial.lean
lean -o Binary.olean Binary.lean
lean -o Classification.olean Classification.lean
lean -o Routing.olean Routing.lean
lean Audit.lean | tee Audit.log
theorems=(
    OMA.disproof
    OMA.MultinomialWitness.monotonicity_fails_every_trial_count
    MultinomialClassification.classification
    MultinomialRouting.average_load
    MultinomialRouting.link_cost_monotone
    MultinomialRouting.routing_monotone
)
for theorem in "${theorems[@]}"; do
    grep -Fxq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" Audit.log
done
BUILD
