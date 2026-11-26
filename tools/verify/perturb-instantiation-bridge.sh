#!/bin/sh
# Measure, for card 4102f131's increment `NUM_INST` and the bridge `NUM_PROV_BOUNDED_INST`, that the
# guards written with it go red on the defects they are for.
#
# 1. A bridge claiming more than is true. With the coverage premise weakened from `w < n` to
#    `w <= n`, the published statement lets variable `n` stay free in the instance, which is then
#    not closed and not something completeness speaks of. The statement is false, and the chain
#    should refuse to build at `NUM_PROV_BOUNDED_INST`, the theorem proved being the one with `<`.
# 2. The test's free-variable walk. With the arity in the end-to-end test lowered from two to one,
#    `v_1` is free in the triangle's graph and not below the arity, and the test should go red at
#    the coverage it discharges by walking the code, rather than reach the bridge: what would make
#    the test vacuous is a coverage premise that holds whatever the code is.
# 3. The cost pin. With `NUM_INST_TRUE` taken out of the facts expected to spend `ETA`, the test
#    of what each fact spends should go red naming it, because the environment at zero is `e` only
#    by `ETA`.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-26, on the tree that became the commit carrying this file: the control
# green at 21 of 21, the tree restored after each perturbation, and all three red.
# 1. All 21 red, every one at `Chain.standard`: "expected the statement published for
#    NUM_PROV_BOUNDED_INST, found" the theorem with `<`. As predicted, and with `### exit 0`.
# 2. One red, the end-to-end test, inside the coverage it discharges but EARLIER than predicted:
#    at the step deriving `0 < bound` by transitivity, which the test builds for a bound of two,
#    "NotOfForm(a proof of the implication's antecedent, 0 < SUC 0 /\ SUC 0 < SUC (SUC 0))". So
#    this shows the walk is built for its bound and cannot pass at another, and NOT that `v_1` is
#    the variable rejected: the run never reached `v_1`.
# 3. One red, the per-fact cost, naming `NUM_INST_TRUE` with `ETA` among what it spends. As
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
LOG="$OUT/instantiation-bridge.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-bridge-claiming-variable-n-may-stay-free" >> "$LOG"
"$P" "$TRUTH" '        "(!w:num. NUM_FREE_FORM w p ==> w < n) ==> " +' \
  '        "(!w:num. NUM_FREE_FORM w p ==> w <= n) ==> " +' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-bridge-claiming-variable-n-may-stay-free" >> "$LOG"

echo "################ 2-the-test-at-one-variable" >> "$LOG"
"$P" "$TEST" '    val bound = term(two)' '    val bound = term("SUC ZERO")' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-test-at-one-variable" >> "$LOG"

echo "################ 3-the-pin-without-eta-at-the-instance" >> "$LOG"
"$P" "$TEST" 'val withEta = Set(Truth.InstanceTrue, Truth.ProvesBoundedInstance' \
  'val withEta = Set(Truth.ProvesBoundedInstance' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-pin-without-eta-at-the-instance" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
