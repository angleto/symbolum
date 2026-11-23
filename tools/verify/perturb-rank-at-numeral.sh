#!/bin/sh
# Measure, for card 4102f131's increment `NUM_RANK` and `NUM_RANK_SUBST_NUMERAL`, that the
# induction hypothesis is what carries the universal that the substitution goes under.
#
# 1. The hypothesis at the body dropped from that case. The two sides then rewrite to
#    `SUC (NUM_RANK (NUM_SUBST_FORM x (NUM_NUMERAL k) v))` and `SUC (NUM_RANK v)`, which nothing
#    else joins, and the chain should refuse to build there, saying the two sides do not meet.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-22, on the tree that became the commit carrying this file: the control
# green at 14 of 14, the tree restored afterwards, and the perturbation as predicted.
# 1. All 14 red, every one at `Chain.standard`: "transitivity: (SUC (NUM_RANK (((NUM_SUBST_FORM
#    x) (NUM_NUMERAL k)) v))) is not (SUC (NUM_RANK v))", the universal's two sides not meeting.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/rank-at-numeral.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-without-the-hypothesis-under-the-binder" >> "$LOG"
"$P" "$TRUTH" '                met(Vector(chained(substitution, passed(notX, stopped, under)), ranking.universal, atV), kept(shape))' \
  '                met(Vector(chained(substitution, passed(notX, stopped, under)), ranking.universal), kept(shape))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-without-the-hypothesis-under-the-binder" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
