#!/bin/sh
# Fire the guards of the recall-size facts of Decision (no card: asked by Angelo on 2026-11-27 for R1
# of the bounded reader in `thinktank/utitlita_e_danno`, the optimal recall size is unimodal).
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own, because one refusal stops the chain from being built and every later fact with it.
#
# WHAT WAS SEEN: not yet run. The reading is written here after the first run, perturbation by
# perturbation, with the refusal each one met.
#
# READ THE LOG, NOT THE EXIT CODE: `testOnly` over an aborted suite has exited 0 before (see
# perturb-decision-lecam.sh). `*** 1 SUITE ABORTED ***` and the refusal under it are the reading.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DECISION=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Decision.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DecisionSpec'
LOG="$OUT/decision-recall.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. RECALL_PERSIST for a reader whose d may grow by two per item, statement and proof together:
#    false (r1_scout.py's control C2 finds readers degrading slower than softmax that are not
#    unimodal), and the arithmetic must refuse it.
# 2. The reader's equation with `d i + 2` for `d i + 1`, in every statement and proof that uses it:
#    the ring identity RECALL_STOP is built on no longer holds, and the arithmetic must refuse it.
# 3. RECALL_SOFTMAX stated for `0 <= c`: false at `c = 0` (every `c + i` at `i = 0` is zero), and
#    the derivation, written for `0 < c`, proves another text.
run() {
  name=$1; from=$2; to=$3
  echo "################ $name" >> "$LOG"
  "$P" "$DECISION" "$from" "$to" -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-persist-d-grows-by-two \
  'd (SUC $i) <= d $i + 1 ==> " +' \
  'd (SUC $i) <= d $i + 2 ==> " +'
run 2-reader-plus-two \
  's"s $i * d $i = s (SUC $i) * (d $i + 1)"' \
  's"s $i * d $i = s (SUC $i) * (d $i + 2)"'
run 3-softmax-c-nonnegative \
  '("!c:real. 0 < c ==> (!i:num. 0 < c + real_of_num i) /\\' \
  '("!c:real. 0 <= c ==> (!i:num. 0 < c + real_of_num i) /\\'

cd "$WT" && git status --porcelain >> "$LOG"
