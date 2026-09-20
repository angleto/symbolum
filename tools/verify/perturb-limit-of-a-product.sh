#!/bin/sh
# Fire the two steps of `CONVERGES_MUL` that a plausible derivation would leave out, card a714187c.
#
# The limit of a product is the limit of a sum with two things added, and both are invisible in the
# statement: the convergence of `s` is spent a THIRD time, at the tolerance `1`, purely to bound
# `abs (s n)`; and two bounds that meet in the middle are brought into one shape by `MUL_SYM`
# before modus ponens can join them. A derivation missing either proves nothing, and `LimitSpec`
# would not say which was missing -- it would say the development does not build.
#
# That is the shape to expect in the log: both are red at the CHAIN and not at an assertion.
# `Limit` is constructed once, so a step that does not close makes every spec over it abort, and
# the message names the refusal rather than a failed comparison.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-20, on the tree that landed this. Control green at 18 tests. Perturbation
# 1 refused with `the standard chain does not build: eliminating an existential needs a theorem
# assuming ... abs (s x - a) < e * inv ((abs a + 1) + (abs b + 1))`, which is the third asking
# being load-bearing named by the proposition it was replaced with. Perturbation 2 refused with
# `expected a proof of the implication's antecedent, found abs (s n) * abs (t n - b) <= (abs a + 1)
# * abs (t n - b)`, which is the un-commuted shape printed beside the one wanted. Both exit 1, and
# the restore was verified clean by the tool.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/limit-product.log"
./tools/sbt -batch "$SPEC" >> "$OUT/limit-product.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/limit-product.log"

# 1. The third asking dropped, by taking the bound on `abs (s n)` from the estimate's own tolerance
# instead of from `1`. Nothing about the perturbed line is false and the sequence really is that
# near its limit past that index; what fails is that `sizeBounded` wants `abs (s n - a) < 1` and is
# handed `abs (s n - a) < e * inv (...)`, which is a different proposition. This is the assertion
# that three indices are three rather than a conservative two, and it is the one a reader who knows
# the textbook proof is most likely to think is an accident.
echo "################ 1-the-bound-taken-from-the-wrong-tolerance" >> "$OUT/limit-product.log"
"$P" "$SOURCE" \
  'withinOne <- rules.spec(one, bodyA).flatMap(rules.mp(_, products.zeroLessOne))' \
  'withinOne <- rules.spec(tolerance, bodyA).flatMap(rules.mp(_, positiveTolerance))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/limit-product.log" 2>&1
echo "### exit $? for 1-the-bound-taken-from-the-wrong-tolerance" >> "$OUT/limit-product.log"

# 2. The commutation removed from the left summand. `leftStep` then ends at `(abs a + 1) * abs (t n
# - b)` where `leftReach` begins at `abs (t n - b) * (abs a + 1)`, which are the same number and not
# the same term, so the schematic implication cannot be discharged against both. This is what the
# docstring's sentence about two theorems modus ponens cannot join asserts, fired.
echo "################ 2-the-commutation-removed" >> "$OUT/limit-product.log"
"$P" "$SOURCE" \
  '        .flatMap(rules.mp(_, sizeBounded))
        .flatMap(theorem =>
          rules
            .specAll(products.symmetric, List(boundA, distanceB))
            .flatMap(rewriteInProposition(_, theorem)))' \
  '        .flatMap(rules.mp(_, sizeBounded))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/limit-product.log" 2>&1
echo "### exit $? for 2-the-commutation-removed" >> "$OUT/limit-product.log"

cd "$WT" && git status --porcelain >> "$OUT/limit-product.log"
