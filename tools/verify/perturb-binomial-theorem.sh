#!/bin/sh
# Fire the three claims the binomial theorem's step makes about itself, card a714187c.
#
# The statement is one line and the step is four congruences, and nothing printed says which of
# them carries a bound, where the coefficient is allowed to run off the diagonal, or that the
# induction hypothesis has to be spent before the linear assembly rather than inside it. Those are
# the three, one perturbation each.
#
# All three are red at the CHAIN, since `Series` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this. Control green at 47 tests, all three
# red at the chain, restore verified clean. Every refusal is `expected a proof of the
# implication's antecedent`, and what each was HANDED is the reading:
#
#   1. `NUM_LT i (SUC n)`, which is the true bound, offered where the crossed lemma wants
#      `NUM_LT n (SUC i)`. The congruence's own bound is right and the arithmetic asked for the
#      other one.
#   2. `NUM_LT n (SUC n)`, offered where the crossed `NUM_CHOOSE_ABOVE` wants
#      `NUM_LT (SUC n) n`. Below the diagonal the entry is not zero and nothing discharges it.
#   3. The whole equation `(x + y) * Power (x + y) n = (x + y) * Sum ...`, offered where the
#      schematic implication wants `l = (p + q) * s`. The left side still names the power, which
#      is the hypothesis not spent, and a linear solver would not have joined the two either.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Series.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesSpec'

echo "################ 0-control" >> "$OUT/binomial.log"
./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/binomial.log"

# 1. The bound read the wrong way round. `NUM_LE_OF_LT_SUC` is what turns the congruence's
# `i < SUC n` into the `i <= n` the arithmetic wants, and the two arguments are a row and a
# column: crossed, it asks for `n <= i`, which is the claim above the diagonal rather than below
# it. This is the one congruence of the four that carries a bound at all, and that fact is
# invisible in the statement.
echo "################ 1-the-bound-crossed" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  'atMost <- rules.specAll(atMostBelow, List(n, index)).flatMap(rules.mp(_, bound))' \
  'atMost <- rules.specAll(atMostBelow, List(index, n)).flatMap(rules.mp(_, bound))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 1-the-bound-crossed" >> "$OUT/binomial.log"

# 2. The entry at the top asked to be zero on the wrong side of the diagonal. `NUM_CHOOSE_ABOVE`
# is spent exactly once, on `NUM_CHOOSE n (SUC n)`, and it is what lets the two sums have one
# length; crossed, it asks for `NUM_CHOOSE (SUC n) n`, which is not zero and which
# `NUM_LT_SUC` cannot discharge.
echo "################ 2-the-diagonal-crossed" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  'rules.specAll(chooseAbove, List(n, successorOfN)).flatMap(rules.mp(_, below)))' \
  'rules.specAll(chooseAbove, List(successorOfN, n)).flatMap(rules.mp(_, below)))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 2-the-diagonal-crossed" >> "$OUT/binomial.log"

# 3. The hypothesis left out of the left-hand side. What the assembly then holds about `l` is an
# equation whose right side still mentions `Power (x + y) n`, and the schematic implication wants
# the narrow sum there. A linear solver would not have joined them either: the two are separate
# atoms to it, which is the whole reason this congruence happens before that call and not in it.
echo "################ 3-the-hypothesis-not-folded" >> "$OUT/binomial.log"
"$P" "$SOURCE" \
  'folded <- Conv.apTerm(scaling, assumed).flatMap(Conv.trans(openedPower, _))' \
  'folded <- Conv.apTerm(scaling, assumed)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binomial.log" 2>&1
echo "### exit $? for 3-the-hypothesis-not-folded" >> "$OUT/binomial.log"

cd "$WT" && git status --porcelain >> "$OUT/binomial.log"
