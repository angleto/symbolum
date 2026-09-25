#!/bin/sh
# Fire the two guards resolution as a link carries, card edc1f509.
#
# 1. The non-vacuity of the lower bound's hypotheses. `ResolvingSpec` states Haken's theorem and
#    asserts it elaborates with nothing free, which a statement whose hypotheses nothing meets would
#    pass exactly as well. The guard is the test that derives both hypotheses at `n = 0`. The
#    perturbation makes the pigeon clause's disjunct ask for a pigeon below zero instead of one at
#    most `n`, so that at `n = 0` neither disjunct can be met: the hole disjunct wants `p < q <= 0`
#    already. Expected: that one test red at the comparison of the witness's claim, since `0 <= 0`
#    is what the derivation has and `0 < 0` is what the perturbed statement asks, and every other
#    test in the file green, the elaboration test included, which is the point.
# 2. That the width is the LARGEST length and not merely some function of the lengths. The step of
#    the recursion is turned into a minimum by swapping the two branches of its `COND`. The
#    definition still type-checks and still defines a function; what cannot go through is
#    `widthSteps`, whose two halves say the old width and the new length are both under the new
#    width. Expected: red at the chain, since the link is built inside `Chain.construct`, so every
#    suite of the module aborts with it.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, on the commit that landed this, rebased onto the line. Control green
# at 16 tests; restore verified clean by `git status --porcelain` at the end. Both predictions met:
#
#   1. one test red, 15 green, at `NotOfForm(the witness's claim, NUM_LE ZERO ZERO /\ ...)`: the
#      derivation had `0 <= 0` for the pigeon and the perturbed statement asked for `0 < 0`. The
#      elaboration test stayed green, which is the whole reason the second test exists.
#   2. red at the chain, the suite aborted, with `modus ponens on an equation: NUM_LE (x x1) (x x1)
#      is not NUM_LE (x x1) (RES_WIDTH x x1)`: inside `widthSteps`, where the guard's branch now
#      says the new width is the new length and the proof still carries the old width across it.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

RESOLVING=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Resolving.scala
SPECFILE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/ResolvingSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ResolvingSpec'
LOG="$OUT/resolving-link.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-a-pigeon-below-zero" >> "$LOG"
"$P" "$SPECFILE" \
  '"(?p:num. NUM_LE p n /\\ " +' \
  '"(?p:num. NUM_LT p 0 /\\ " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-a-pigeon-below-zero" >> "$LOG"

echo "################ 2-the-width-a-minimum" >> "$LOG"
"$P" "$RESOLVING" \
  'COND (NUM_LE ((k:num->num) i) w) w (k i)' \
  'COND (NUM_LE ((k:num->num) i) w) (k i) w' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-width-a-minimum" >> "$LOG"

git status --porcelain -- "$RESOLVING" "$SPECFILE" >> "$LOG"
echo "### restore checked" >> "$LOG"
