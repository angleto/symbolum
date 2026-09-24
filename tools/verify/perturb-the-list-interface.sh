#!/bin/sh
# Fire the three perturbations the delivery of card 5d59c308 (the list interface, `Listing`)
# suggested in its test plan and did not run.
#
# 1. The tail's conditional taken away: `WORD_MAKE (PRE |w|) (\i. WORD_NTH w (SUC i))`. Well typed,
#    and true in the model, since `WORD_NTH` past the length is the padding anyway; what the
#    conditional is for is discharging `WORD_MAKE`'s padding premise by `COND_FALSE` alone.
# 2. The tail's guard one place too far: `NUM_LT i (WORD_LENGTH w)` where `PRE (WORD_LENGTH w)`
#    stands. The guard and the bound of `WORD_MAKE` then disagree.
# 3. The cons put on the right: `WORD_CONCAT w (WORD_SINGLETON x)`, which is a snoc and makes
#    `LIST_HEAD_CONS` false.
#
# WHAT WAS SEEN, 2026-09-24, on 712964af plus the verification's own test commit. Control green at
# 18 tests (ListingSpec and FoldingSpec). All three red at the chain, both suites aborted:
#
#   1. `expected an application of COND to three arguments, found ((WORD_NTH ((LIST_CONS x) w))
#      (SUC i))`. Refused where `theTail` takes the body apart, which is a syntactic refusal and
#      not the padding premise failing.
#   2. `transitivity: (COND (NUM_LT i (WORD_LENGTH (LIST_CONS x w))) ...) is not (COND (NUM_LT i
#      (PRE (WORD_LENGTH (LIST_CONS x w)))) ...)`. The bound and the guard no longer meet.
#   3. `transitivity: (WORD_LENGTH (WORD_CONCAT w (WORD_SINGLETON x))) is not (WORD_LENGTH
#      (WORD_CONCAT (WORD_SINGLETON x) w))`. Refused at LIST_CONS_LENGTH, whose statement is
#      still TRUE for a snoc: the proof script's shape stops it before the false fact
#      (LIST_HEAD_CONS) is reached, so this red says the definition moved and not that the kernel
#      met a falsehood.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LISTING=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Listing.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ListingSpec garden.xeno.symbolum.theories.FoldingSpec'
LOG="$OUT/the-list-interface.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-tail-without-its-conditional" >> "$LOG"
"$P" "$LISTING" \
  '"(\\i:num. COND (NUM_LT i (PRE (WORD_LENGTH w))) (WORD_NTH w (SUC i)) WORD_PAD)")' \
  '"(\\i:num. WORD_NTH w (SUC i))")' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-tail-without-its-conditional" >> "$LOG"

echo "################ 2-the-guard-one-too-far" >> "$LOG"
"$P" "$LISTING" \
  'COND (NUM_LT i (PRE (WORD_LENGTH w)))' \
  'COND (NUM_LT i (WORD_LENGTH w))' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-guard-one-too-far" >> "$LOG"

echo "################ 3-the-cons-on-the-right" >> "$LOG"
"$P" "$LISTING" \
  'WORD_CONCAT (WORD_SINGLETON x) w"' \
  'WORD_CONCAT w (WORD_SINGLETON x)"' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-cons-on-the-right" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
