#!/bin/sh
# Fire the three claims `SUM_DIAGONAL`'s derivation makes about why it waited, card a714187c.
#
# The lemma is an induction, and an induction that goes green tells a reader nothing about which
# of the parts around it were load-bearing. Three were, and each is a sentence in the docstring
# rather than a step anybody can see from the statement: that the congruence has to be the
# BOUNDED one, that the unconditional `NUM_SUC_SUB_SELF` has to be a rewrite rule because the
# conditional fact cannot be, and that the induction hypothesis has to be put through the rules
# before it is offered as one.
#
# All three are red at the CHAIN and not at an assertion: `Series` is constructed once, so a step
# that does not close makes every spec over it abort. That is the shape to expect in the log.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-20, on the tree that landed this. Control green at 46 tests, all three
# red at the chain, restore verified clean.
#
#   1. Refused EARLIER than this file predicted, and the difference is worth keeping. The comment
#      below says the obligation cannot be discharged; what actually happens is that the
#      derivation goes looking for the guard `NUM_LT i n ==>` in the congruence's antecedent and
#      there is none, so it refuses with `expected a universal quantification, found (==> (!...)
#      ...)`. The unbounded lemma's antecedent is `!i. f i = g i` and the step reads it as an
#      implication under a binder. Same conclusion, one step sooner, and the prediction was about
#      the mathematics where the refusal is about the shape.
#   2. `... is not equal to ...` with `NUM_SUB (SUC n) n` still standing on the right-hand side,
#      which is the last row's length unreduced and is exactly what was predicted.
#   3. The refusal this defect actually produced while the lemma was being written: the two sides
#      differ in one summand, the left carrying `Sum (\k. Sum (\i. f i (k - i)) k + f k ZERO) n`
#      where the right carries `Sum (\i. Sum (\j. f i j) (n - i)) n`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Series.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesSpec'

echo "################ 0-control" >> "$OUT/triangle.log"
./tools/sbt -batch "$SPEC" >> "$OUT/triangle.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/triangle.log"

# 1. The unbounded congruence in place of the bounded one. `SUM_CONGRUENCE` asks that the two
# summands agree at EVERY index, and they do not: at any `i` above `n` the row has length `ZERO`
# on one side and `SUC ZERO` on the other. So the obligation cannot be discharged and the step
# refuses. This is `SUM_CONGRUENCE_BELOW`'s own docstring being spent, which predicted that the
# first real consumer of a bounded rewrite would meet this wall.
echo "################ 1-the-unbounded-congruence" >> "$OUT/triangle.log"
"$P" "$SOURCE" \
  'driver, withProd, notation, recurrences ++ differences, additive, congruenceBelow,' \
  'driver, withProd, notation, recurrences ++ differences, additive, congruence,' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/triangle.log" 2>&1
echo "### exit $? for 1-the-unbounded-congruence" >> "$OUT/triangle.log"

# 2. The unconditional subtraction fact dropped from the rule set. The last row of the triangle
# has length `SUC n - n` and nothing else reduces it, so the right-hand side keeps a difference
# the left-hand side has already spent. The conditional `NUM_SUC_SUB` cannot stand in: a rule is
# an equation and `Rewrite.Rule.of` refuses an implication, which is the whole reason the second
# lemma exists in `Peano`.
echo "################ 2-the-last-row-unreduced" >> "$OUT/triangle.log"
"$P" "$SOURCE" \
  'differences <- Rewrite.Rule.all(logic, Vector(subSelf, stepMinusSelf))' \
  'differences <- Rewrite.Rule.all(logic, Vector(subSelf))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/triangle.log" 2>&1
echo "### exit $? for 2-the-last-row-unreduced" >> "$OUT/triangle.log"

# 3. The induction hypothesis offered raw. Its left side is a sum whose summand is a sum of
# length `SUC k`, so `SUM_SUC` fires on it under the binder and the goal never carries the shape
# the hypothesis is written in. This is the one that actually bit, and the refusal names the two
# sides differing in exactly that summand.
echo "################ 3-the-hypothesis-not-normalised" >> "$OUT/triangle.log"
"$P" "$SOURCE" \
  'hypothesisRule <- Rewrite.Rule.of(logic, carried)' \
  'hypothesisRule <- Rewrite.Rule.of(logic, opened.hypothesis)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/triangle.log" 2>&1
echo "### exit $? for 3-the-hypothesis-not-normalised" >> "$OUT/triangle.log"

cd "$WT" && git status --porcelain >> "$OUT/triangle.log"
