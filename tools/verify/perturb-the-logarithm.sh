#!/bin/sh
# Fire the guards of card 7f6ac0d3, the first facts about ln, at the defects they are for.
#
# `Logarithm` declares nothing and publishes twelve facts about `exp` and `ln`. What can go wrong is
# a published statement that says more than was derived, and a logarithm defined as the inverse of
# something other than the exponential while its facts are still claimed. Each perturbation below is
# one of those, and each is caught before any test body runs: `Logarithm.construct` checks every
# fact against the text it is published under, and the derivation of `EXP_LN` reads the definition
# back, so a broken logarithm is a chain that does not build.
#
# What this does NOT fire is `LogarithmSpec`'s refutation of the estimate at `h = 8`. It is a
# derivation in the spec about a statement nobody publishes, which is its point: it says the radius
# carries weight, and no edit of the source makes the unconditional statement published.
#
# The strings are literal and were unique when this was written. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/logarithm.log"
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Logarithm.scala
DEFINITIONS=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Transcendental.scala
SPECS='theories/testOnly garden.xeno.symbolum.theories.LogarithmSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The estimate published at a radius twice as wide as the one derived.
# Expect red on: LogarithmSpec aborted, the chain refusing with `EXP_NEAR_ONE as it is written`
run "1-estimate-radius-widened" "$SOURCE" \
  'NearOne -> "!h:real. abs h <= 1 / 2 ==> abs (exp h - 1) <= 2 * abs h",' \
  'NearOne -> "!h:real. abs h <= 1 ==> abs (exp h - 1) <= 2 * abs h",' \
  -- ./tools/sbt -batch "$SPECS"

# 2. The logarithm defined as the inverse of the exponential shifted by one, so `EXP_ONTO` no
#    longer says its choice is satisfiable at every positive number.
# Expect red on: LogarithmSpec aborted, the chain refusing to build in `Logarithm`'s `EXP_LN`
run "2-ln-of-the-wrong-function" "$DEFINITIONS" \
  'val LogarithmBody: String = "\\y:real. select (\\x:real. exp x = y)"' \
  'val LogarithmBody: String = "\\y:real. select (\\x:real. exp x + 1 = y)"' \
  -- ./tools/sbt -batch "$SPECS"

echo "### both fired" >> "$LOG"
git status --porcelain >> "$LOG"
