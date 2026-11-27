#!/bin/sh
# Measure, for card 4102f131's increment `NUM_FST_REPR` and `NUM_SND_REPR`, with the walk widened to
# the bounded universal, that the guards written with them go red on the defects they are for.
#
# 1. The walk's bound. With the first projection's statement claiming one variable put for rather
#    than two, `v_1` is free in the graph and not below the bound read off that statement, and the
#    walk should refuse at it, so the chain should not build.
# 2. The binders' guards. With the freeness walk forgetting the guard `~(j = w)` of the binder it
#    has just passed, the quantified `v_2` and the order's witness `v_3` read as free, and neither
#    is below two, so the walk should refuse at one of them and the chain should not build: what
#    would make the coverage wrong in the other direction is a walk that never looks at binders,
#    and that one cannot be seen on a graph whose bound variables are all below the arity.
# 3. The discrimination test. With the second graph's holding at one read through the first
#    graph's truth fact, the test should go red at its reading: the first graph fails at one, so a
#    test that passed both ways would not be telling the two slots apart.
# 4. The cost pin. With `NUM_FST_REPR` taken out of the facts expected to spend `ETA`, the test of
#    what each fact spends should go red naming it.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-27, on the tree that became the commit carrying this file, under a load
# of about 30 on 8 cores: the control green at 23 of 23, the tree restored after each
# perturbation, and all four red where predicted.
# 1. All 23 red, every one at the walk refusing `v_1`: "a variable below the bound the
#    representation states, found NUM_ONE". With `### exit 0`, which is card f0016ec8.
# 2. All 23 red, every one at the walk refusing `NUM_BIT0 NUM_ONE`, the quantified `v_2`, which
#    is the first bound variable the walk reaches; the witness `v_3` is never reached. Also with
#    `### exit 0`.
# 3. One red, the discrimination test, at its reading of the truth fact: `SUC ZERO = NUM_FST
#    (SUC ZERO)` against `SUC ZERO = NUM_SND (SUC ZERO)`, before any corollary. As predicted.
# 4. One red, the per-fact cost, `NUM_FST_REPR` spending `ETA, INFINITY, SELECT`. As predicted.
#
# READ THE LOG, NOT THE `### exit` LINES: under sbt 2.0.9 `testOnly` can exit 0 over a failure
# whose message is long, and "the standard chain does not build" is. Mycelium card f0016ec8.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
TEST=modules/theories/src/test/scala/garden/xeno/symbolum/theories/TruthSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/projections.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-first-projection-at-one-variable" >> "$LOG"
"$P" "$TRUTH" '(NUM_INST 2 s NUM_FST_GRAPH)) /\\' '(NUM_INST 1 s NUM_FST_GRAPH)) /\\' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-first-projection-at-one-variable" >> "$LOG"

echo "################ 2-the-binders-guard-forgotten" >> "$LOG"
"$P" "$TRUTH" 'inRange(passed, guards.updated(guard, denied))' 'inRange(passed, guards)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-binders-guard-forgotten" >> "$LOG"

echo "################ 3-the-second-read-through-the-first" >> "$LOG"
"$P" "$TEST" 'val secondAtOne = graphHolds(Truth.SecondGraphTrue, atOne,' \
  'val secondAtOne = graphHolds(Truth.FirstGraphTrue, atOne,' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-second-read-through-the-first" >> "$LOG"

echo "################ 4-the-pin-without-eta-at-the-first-projection" >> "$LOG"
"$P" "$TEST" 'Truth.CodeRepresented, Truth.FirstRepresented,' 'Truth.CodeRepresented,' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-pin-without-eta-at-the-first-projection" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
