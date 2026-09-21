#!/bin/sh
# Fire the three mistakes the nested induction can make and still typecheck, card a714187c.
#
# `NUM_CHOOSE_FACTORIAL` is two inductions over Pascal's recurrence, and the two hypotheses it
# uses differ only in which of the two indices is a successor. Every term in sight is a `num`,
# so exchanging them, or opening one of them with the wrong rule set, is well typed and changes
# which claim is being carried.
#
# All three are red at the CHAIN, since `Coding` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 12 tests, all three red at the chain, restore
# verified clean.
#
#   1 and 2 both refuse inside `Semiring`, which prints the normal form the two sides reached
#   and not the step that produced them. That is the honest shape of the failure and it is also
#   the least readable of the three: what a reader can tell from it is that the identity did not
#   close, and which hypothesis was wrong has to come from the perturbation's own line. The first
#   is the mistake this derivation actually made before the chain caught it.
#
#   3. `NUM_FACT x * NUM_CHOOSE x x is not equal to NUM_FACT x`, which is the clearest of the
#      three and says exactly what the exchange cost: with `NUM_CHOOSE_ZERO` in the diagonal's
#      place the coefficient never becomes one, and the base of the outer induction is left
#      asserting that a factorial times it is itself.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Coding.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CodingSpec'

echo "################ 0-control" >> "$OUT/binomial.log"
./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/binomial.log"

# 1. The outer hypothesis opened without Pascal. Rewriting the goal opens the coefficient twice,
# so what stands where this hypothesis has to match is `C q a + C q (SUC a)` and not
# `C (SUC q) (SUC a)`. Both are true statements about the triangle; only one of them is the
# shape the goal left behind, and this is the mistake the derivation actually made.
echo "################ 1-the-outer-hypothesis-unopened" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  '.rewrite(arithmetic ++ Vector(factorialSuccessorRule, pascalRule), fromOuter.conclusion)' \
  '.rewrite(arithmetic :+ factorialSuccessorRule, fromOuter.conclusion)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 1-the-outer-hypothesis-unopened" >> "$OUT/binomial.log"

# 2. The outer hypothesis read at the row rather than at its successor. `spec(here, ...)` is what
# makes it the claim at `(SUC a, b)`; at `a` it is the claim at `(a, b)`, which is true, is the
# hypothesis one step back, and carries a factorial the goal does not have.
echo "################ 2-the-outer-hypothesis-off-by-one" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  'fromOuter <- rules.spec(here, outerHypothesis)' \
  'fromOuter <- rules.spec(innerStep.variable, outerHypothesis)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 2-the-outer-hypothesis-off-by-one" >> "$OUT/binomial.log"

# 3. The two edges exchanged. The base of the outer induction is `j = 0`, which is the diagonal,
# and the base of the inner one is `i = 0`, which is `NUM_CHOOSE_ZERO`. Both are facts about an
# edge of the triangle and each closes the other's case in no way at all.
echo "################ 3-the-edges-exchanged" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  'arithmetic ++ Vector(diagonalRule, factorialZeroRule), baseStripped._2)(settled)' \
  'arithmetic ++ Vector(noneRule, factorialZeroRule), baseStripped._2)(settled)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 3-the-edges-exchanged" >> "$OUT/binomial.log"

cd "$WT" && git status --porcelain >> "$OUT/binomial.log"
