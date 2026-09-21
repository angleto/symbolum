#!/bin/sh
# Fire the two claims the additive route makes about itself, card a714187c.
#
# Both facts here are proved WITHOUT a case split, and in both the reason is the same: the order
# on `num` is an existential over a sum, so a statement about `<` becomes a statement about `+`
# and the branch disappears. That is a claim about the proof and not about the theorem, so
# nothing printed can carry it and no assertion over the statements can fail for it.
#
# What can is the derivation refusing when the two steps that carry the weight are taken away:
# the hypothesis used at ONE column where the induction needs it at two, and the recurrence of
# addition read in the direction that does not close.
#
# Both are red at the CHAIN, since `Peano` is constructed once. The control is the run before
# them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this. Control green at 34 tests, both red at
# the chain, restore verified clean.
#
#   1. `expected a closed equation, found NUM_CHOOSE n (SUC (SUC (n + j))) = ZERO`. That term is
#      the SECOND of the two entries Pascal produces, left standing because the hypothesis was
#      offered at the column below it. The refusal names the entry rather than the column, which
#      is as close as a message here gets to saying "the induction needed the row twice".
#   2. `transitivity: SUC (i + d) is not (SUC i) + d`. The two terms that do not meet, printed
#      beside each other, which is the whole content of the step that makes the two existentials
#      share a witness.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Peano.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.PeanoSpec'

echo "################ 0-control" >> "$OUT/diagonal.log"
./tools/sbt -batch "$SPEC" >> "$OUT/diagonal.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/diagonal.log"

# 1. The hypothesis taken at one column instead of two. Pascal's rule turns one entry of the row
# above into two entries of the row below, at the column and at the one past it, so an induction
# that offers its hypothesis at a single column settles one of them and stalls on the other. This
# is the whole reason the column is quantified INSIDE the predicate, and it is invisible in the
# statement, which says nothing about how the row was reached.
echo "################ 1-the-hypothesis-at-one-column" >> "$OUT/diagonal.log"
"$P" "$SOURCE" \
  'above <- rules.spec(nextColumn, hypothesis).flatMap(normalise(shared))' \
  'above <- rules.spec(column, hypothesis).flatMap(normalise(shared))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/diagonal.log" 2>&1
echo "### exit $? for 1-the-hypothesis-at-one-column" >> "$OUT/diagonal.log"

# 2. The recurrence read the wrong way round in the crossing between the two orders. `SUC i + d`
# and `SUC (i + d)` are the same number and the equation between them has a direction; composed
# without the turn, the middle terms do not meet and transitivity refuses. It is the step that
# makes the two existentials share a witness, which is the whole of that proof.
echo "################ 2-the-recurrence-not-turned" >> "$OUT/diagonal.log"
"$P" "$SOURCE" \
  'stepped <- Conv.sym(pushed).flatMap(Conv.trans(_, reaches))' \
  'stepped <- Conv.trans(pushed, reaches)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/diagonal.log" 2>&1
echo "### exit $? for 2-the-recurrence-not-turned" >> "$OUT/diagonal.log"

cd "$WT" && git status --porcelain >> "$OUT/diagonal.log"
