#!/bin/sh
# Measure, for card 4102f131's increment `NUM_BOUNDED_SUBST_NUMERAL`, that it is the numeral being
# put for the variable that keeps a formula in the bounded class, rather than any term.
#
# 1. A variable `v_k` put for `x` instead of the numeral of `k`. A bound that is `v_x` then becomes
#    `v_k`, which is in the class only when `k` is neither the quantified index nor the order's
#    witness, so the closure is false in general. The chain should refuse to build at the variable
#    bound's case, where the substituted bound is offered as the numeral of `k` and is not it.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-22, on the tree that became the commit carrying this file: the control
# green at 13 of 13, the tree restored afterwards, and the perturbation as predicted.
# 1. All 13 red, every one at `Chain.standard`: "expected a proof of NUM_SUBST_TERM x
#    (NUM_CODE ZERO k) c = NUM_NUMERAL k, found a proof of ... = NUM_CODE ZERO k", the variable
#    bound's case offered `v_k` where the class wants the numeral of `k`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/bounded-at-numeral.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-a-variable-for-the-variable" >> "$LOG"
"$P" "$TRUTH" '      val nk = numeral(k) // closed, so a bound it replaces is a numeral, which the class takes' \
  '      val nk = code(0, k) // closed, so a bound it replaces is a numeral, which the class takes' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-a-variable-for-the-variable" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
