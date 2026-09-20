#!/bin/sh
# Fire the four cases of `ABS_MUL` at the defect a symmetric statement would hide, card a714187c.
#
# `abs (x * y) = abs x * abs y` is symmetric in a way its derivation is not: the four cases each
# pair a sign of the product with two distances, and a derivation that crossed two of them reaches
# a theorem that looks exactly the same. `MagnitudeSpec` compares the printed statement and cannot
# see it. What can is the assembly refusing, and these two perturbations are what show that it
# does rather than quietly agreeing.
#
# Both are red at the CHAIN, not at an assertion: `Magnitude` is built once and a case that does
# not close makes the whole development refuse, so every spec over it aborts. That is the shape to
# expect in the log.
#
# The control is the run before them, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Magnitude.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.MagnitudeSpec'

echo "################ 0-control" >> "$OUT/abs-product.log"
./tools/sbt -batch "$SPEC" >> "$OUT/abs-product.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/abs-product.log"

# 1. The two mixed cases crossed. Both identities are TRUE ring identities, so nothing here is a
# false step: what breaks is that the case with `x` non-negative and `y` below zero now ends at
# `(-x) * y` while its two distances multiply to `x * (-y)`, and the transitivity refuses. A
# derivation that had been written with the crossing in place would have been refused the same
# way, which is what this shows.
echo "################ 1-the-mixed-cases-crossed" >> "$OUT/abs-product.log"
"$P" "$SOURCE" \
  'positiveTimesNegative, false, absXPositive, absYNegative, "-(x:real * y:real) = x * (-y)")' \
  'positiveTimesNegative, false, absXPositive, absYNegative, "-(x:real * y:real) = (-x) * y")' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/abs-product.log" 2>&1
echo "### exit $? for 1-the-mixed-cases-crossed" >> "$OUT/abs-product.log"

# 2. The sign of the product read the other way in one case. `ABS_OF_NONNEG` is then applied to a
# product the case knows to be at most zero, and modus ponens refuses against a hypothesis that is
# `x * y <= 0` where `0 <= x * y` is wanted. This is the half that says the two sign facts are
# doing the work rather than being decoration.
echo "################ 2-the-sign-of-the-product-flipped" >> "$OUT/abs-product.log"
"$P" "$SOURCE" \
  'whenPositiveNegative <- caseOf(
        positiveTimesNegative, false,' \
  'whenPositiveNegative <- caseOf(
        positiveTimesNegative, true,' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/abs-product.log" 2>&1
echo "### exit $? for 2-the-sign-of-the-product-flipped" >> "$OUT/abs-product.log"

cd "$WT" && git status --porcelain >> "$OUT/abs-product.log"
