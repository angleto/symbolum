#!/bin/sh
# Fire the two steps that carry the Cauchy product's finite reduction, card a714187c.
#
# Both facts here are the diagonal and `SUM_ADD` pointed at a product, and neither is an
# induction, so there is very little to go wrong and exactly two places where it can: the row of
# the triangle is collapsed by scaling on the LEFT, since `a i` is what does not depend on the
# index the row runs over; and the gap is split off by naming the corner and the row in that
# order, since `SUM_ADD` puts the two summands where it is told.
#
# Both are red at the CHAIN, since `Series` is constructed once. The control is the run before
# them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this. Control green at 48 tests, both red at
# the chain, restore verified clean.
#
#   1. `expected a proof of the implication's antecedent, found !x. Sum (\y. a x * a y) (n - x) =
#      a x * Sum a (n - x)`. The obligation printed is a claim about `a` where the row of the
#      triangle is a claim about `b`, which is the perturbation named by what it asks for rather
#      than by what failed.
#   2. `transitivity: ... is not ...`, with the corner and the row printed in the two places they
#      were exchanged. Both sides are true of something; what breaks is that the chain no longer
#      meets in the middle, and the `Linarith` step at the end would have called the triangle the
#      gap.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Series.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesSpec'

echo "################ 0-control" >> "$OUT/cauchy.log"
./tools/sbt -batch "$SPEC" >> "$OUT/cauchy.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/cauchy.log"

# 1. The row collapsed against the wrong sequence. A row of the triangle is `a i` times a partial
# sum of `b`, and `SUM_SCALE` takes the factor out because `a i` does not move as the row runs;
# handed `a` in that place it is asked to take out something that does, and the congruence's
# obligation is then a claim about a different sum.
echo "################ 1-the-row-scaled-against-the-wrong-sequence" >> "$OUT/cauchy.log"
"$P" "$SOURCE" \
  'rules.specAll(scaled, List(factor, b, length)).flatMap(normalised)' \
  'rules.specAll(scaled, List(factor, a, length)).flatMap(normalised)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cauchy.log" 2>&1
echo "### exit $? for 1-the-row-scaled-against-the-wrong-sequence" >> "$OUT/cauchy.log"

# 2. The two summands of the split named the other way round. `SUM_ADD` is told which summand is
# which, and the whole point of the gap is that it is the corner FIRST and the triangle second:
# crossed, what comes out is the same number written so that the `Linarith` step at the end
# subtracts the corner and calls the triangle the gap.
echo "################ 2-the-split-the-other-way-round" >> "$OUT/cauchy.log"
"$P" "$SOURCE" \
  'rules.specAll(additive, List(cornerBody, rowsBody, n))' \
  'rules.specAll(additive, List(rowsBody, cornerBody, n))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cauchy.log" 2>&1
echo "### exit $? for 2-the-split-the-other-way-round" >> "$OUT/cauchy.log"

cd "$WT" && git status --porcelain >> "$OUT/cauchy.log"
