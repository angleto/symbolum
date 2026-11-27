#!/bin/sh
# Measure, for card 4102f131's increment `NUM_TRI_REPR`, `NUM_PAIR_REPR` and `NUM_CODE_REPR`, that
# the guards written with them go red on the defects they are for.
#
# 1. The walk's bound. With the pairing's statement claiming two variables put for in its first
#    half rather than three, `v_2` is free in the graph and not below the bound read off that
#    statement, and the walk should refuse at it, so the chain should not build: what would make
#    the coverage vacuous is a walk that puts every index below whatever bound it is handed.
# 2. The end-to-end test's reading. With the pairing's refutation at one fed the graph's truth
#    there unnegated, the corollary's antecedent is not what the truth fact gives, and that case
#    should go red: what would make the test a restatement is an antecedent it never had to meet.
# 3. The cost pin. With `NUM_CODE_REPR` taken out of the facts expected to spend `ETA`, the test of
#    what each fact spends should go red naming it, since it spends the bridge's.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-27, on the tree that became the commit carrying this file: the control
# green at 22 of 22, the tree restored after each perturbation, and all three red.
# 1. All 22 red, every one at the walk refusing `v_2` as not below the bound, which the run then
#    printed as "a variable below the bound (NUM_BIT0 NUM_ONE)" and which reads "a variable below
#    the bound the representation states" since, the census of refusals in `NotationBoundarySpec`
#    wanting a literal. As predicted, and with `### exit 0`.
# 2. One red, the end-to-end test, but EARLIER than predicted: at reading the graph's truth fact
#    against the refutation, `TermsDiffer` between `NUM_TRUE NUM_PAIR_GRAPH (\x. SUC ZERO)` and its
#    negation, so the run never reached the corollary. This shows the test's reading of the truth
#    fact is oriented by the case and cannot pass both ways, and NOT that the corollary's
#    antecedent is what refuses the wrong one: that is the kernel's modus ponens, not this test.
# 3. One red, the per-fact cost, naming `NUM_CODE_REPR` with `ETA, INFINITY, SELECT`. As
#    predicted.
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
LOG="$OUT/representations.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-pairing-at-two-variables" >> "$LOG"
"$P" "$TRUTH" '(NUM_INST 3 s NUM_PAIR_GRAPH)) /\\' '(NUM_INST 2 s NUM_PAIR_GRAPH)) /\\' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-pairing-at-two-variables" >> "$LOG"

echo "################ 2-the-refutation-fed-unnegated" >> "$LOG"
"$P" "$TEST" 'meaning(Truth.PairGraphTrue, atOne, pairFailsAtOne, negated = true)' \
  'meaning(Truth.PairGraphTrue, atOne, pairFailsAtOne, negated = false)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-refutation-fed-unnegated" >> "$LOG"

echo "################ 3-the-pin-without-eta-at-the-constructor" >> "$LOG"
"$P" "$TEST" 'Truth.TriangleRepresented, Truth.PairRepresented, Truth.CodeRepresented)' \
  'Truth.TriangleRepresented, Truth.PairRepresented)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-pin-without-eta-at-the-constructor" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
