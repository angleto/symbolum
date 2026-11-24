#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PAIR_GRAPH` and `NUM_CODE_GRAPH`, that each graph's
# truth theorem rests on the formula being the doubled closed form, all of it, and that the shared
# proof reads the arguments in the order the function takes them.
#
# 1. The pair's last summand. With `(v1 + v1)` dropped from the doubled pair, the pairing's graph
#    reads `v0 + v0 = (v1 + v2) * S (v1 + v2)`, which is not twice the pair, and the chain should
#    refuse to build at `NUM_PAIR_GRAPH_TRUE`, where the specialised closed form and the evaluated
#    formula no longer have one right side.
# 2. The constructor's successors. With the two successors dropped, the constructor's graph is the
#    pair's, and the chain should refuse to build at `NUM_CODE_GRAPH_TRUE` for the same reason.
# 3. The argument order. `graphByDoubling` says that a closed form specialised in another order
#    than the function's is refused rather than proving another statement. With the arguments
#    reversed, the triangle is unaffected, having one, and the chain should refuse to build at the
#    pairing's graph.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-24, on the tree that became the commit carrying this file: the control
# green at 20 of 20, the tree restored after each perturbation, and all three as predicted.
# 1. All 20 red, every one at `Chain.standard`: "transitivity: ((NUM_MUL ...) (SUC ...)) is not
#    ((NUM_ADD ((NUM_MUL ...) (SUC ...))) ((NUM_ADD (f NUM_ONE)) (f NUM_ONE)))", the evaluated graph
#    missing the `v1 + v1` the closed form has.
# 2. All 20 red, every one at `Chain.standard`: the same transitivity refused, with
#    `SUC (SUC (...))` on the side of the closed form and not on the formula's.
# 3. All 20 red, every one at `Chain.standard`: "transitivity: NUM_PAIR (f 1) (f 2) + ... is not
#    NUM_PAIR (f 2) (f 1) + ...", the reversed specialisation refused rather than proving another
#    statement, as `graphByDoubling` says.
#
# READ THE LOG, NOT THE `### exit` LINES. All three runs printed `*** 20 TESTS FAILED ***` and then
# `[success]`, and every `### exit` read 0: under sbt 2.0.9 a forked test failing with a message
# longer than somewhere between 60 000 and 70 000 characters reaches sbt as no failure at all, and
# "the standard chain does not build" prints whole terms. Measured on `scan` the same day and
# recorded as Mycelium card f0016ec8.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/pair-code-graph.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-pair-without-its-last-summand" >> "$LOG"
"$P" "$TRUTH" '    s"(NUM_CODE 3 (NUM_PAIR $product $first))"' \
  '    product' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-pair-without-its-last-summand" >> "$LOG"

echo "################ 2-the-constructor-without-its-successors" >> "$LOG"
"$P" "$TRUTH" '(NUM_CODE 2 (NUM_CODE 2 $PairDoubledText))' \
  '$PairDoubledText' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-constructor-without-its-successors" >> "$LOG"

echo "################ 3-the-arguments-reversed" >> "$LOG"
"$P" "$TRUTH" 'rules.specAll(doubled, arguments(functionOfArguments))' \
  'rules.specAll(doubled, arguments(functionOfArguments).reverse)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-arguments-reversed" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
