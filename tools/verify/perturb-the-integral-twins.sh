#!/bin/sh
# Fire the census of card 6257d0da, every two-sided interval continuity hypothesis with a `_WITHIN` twin, at the defect it is for.
#
# `IntegralWithinSpec` holds the census: every library fact with an antecedent `!x. p x ==> ... ==>
# continuous f x` must have a fact named with `_WITHIN` appended, stated with `continuous_within`,
# or be listed in `Pending` with the card that owes it. The delivery said it had not been seen red.
# The defect it is for is a twin going missing, or a new two-sided fact landing without one, and
# the three perturbations below are those two and the edge of what the census reads.
#
#   1. A twin goes missing: `CONTINUOUS_INTEGRAL_WITHIN` is published under another name.
#      Expect red on the census, naming `CONTINUOUS_INTEGRAL`.
#   2. The pending entry is dropped: `TAYLOR` is then a two-sided fact without a twin and without a
#      card. Expect red on the census, naming `TAYLOR`, which also shows the selector sees TAYLOR's
#      hypothesis through its two implications.
#   3. The edge, and the expectation is GREEN: `HAS_INTEGRAL_DERIVATIVE_WITHIN` is published under
#      another name. Its two-sided form's hypothesis is a two-sided DERIVATIVE over the interval,
#      which the census does not count by its own docstring (card 3caa8541 owns that class), so the
#      census stays green. This is the measurement of the scope limit, not a guard firing.
#
# The strings are literal. perturb.sh REFUSES a perturbation that did not apply rather than running
# against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/integral-twins.log"
THEORIES=modules/theories/src/main/scala/garden/xeno/symbolum/theories
TESTS=modules/theories/src/test/scala/garden/xeno/symbolum/theories
CENSUS='theories/testOnly garden.xeno.symbolum.theories.IntegralWithinSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$CENSUS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

run "1-a-twin-goes-missing" "$THEORIES/Integral.scala" \
  'val ContinuousIntegralWithin: String = "CONTINUOUS_INTEGRAL_WITHIN"' \
  'val ContinuousIntegralWithin: String = "CONTINUOUS_INTEGRAL_RELATIVE"' \
  -- ./tools/sbt -batch "$CENSUS"

run "2-the-pending-entry-is-dropped" "$TESTS/IntegralWithinSpec.scala" \
  'val Pending = Map("TAYLOR" -> "3b7c74be")' \
  'val Pending = Map.empty[String, String]' \
  -- ./tools/sbt -batch "$CENSUS"

run "3-a-derivative-twin-goes-missing-expect-green" "$THEORIES/Integral.scala" \
  'val HasFundamentalWithin: String = "HAS_INTEGRAL_DERIVATIVE_WITHIN"' \
  'val HasFundamentalWithin: String = "HAS_INTEGRAL_DERIVATIVE_RELATIVE"' \
  -- ./tools/sbt -batch "$CENSUS"

echo "### all ran" >> "$LOG"
git status --porcelain >> "$LOG"
