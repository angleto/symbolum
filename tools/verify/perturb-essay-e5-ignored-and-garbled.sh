#!/bin/sh
# Fire the guards of card 1535fdb7's last two items, essay case E5: the value at `phi = 1/10` with
# the rule that ignores `g`, and `7/20 <= 9/16` as an instance of `BLACKWELL_GARBLING`.
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own, because one refusal ends the E5 test and the next would never be asked.
#
# WHAT WAS SEEN, 2026-11-10, on the tree that landed this. Control green (DecisionSpec 9); every
# perturbation red on the E5 test alone, 8 of 9, restores verified, tree clean after.
#
#   1. Refused by the closing arithmetic: `7/21` and the derived value differ as polynomials.
#   2. Refused at the last step, where `s = g` is left to close and nothing proves it; the message
#      is the real-typed closer refusing a `num` equation, which is how that step says no.
#   3. Refused where the rows proved for a weight of one meet the unfolded `CHANNEL` of a garbling
#      of weight two: the hypothesis of `BLACKWELL_GARBLING` is not discharged.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

CASE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/EssayCase.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DecisionSpec'
LOG="$OUT/essay-e5.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. A wrong value at phi = 1/10: the derivation must refuse it, not prove it.
# 2. A wrong rule: the reader following `g` rather than `s` at phi = 1/10.
# 3. A garbling that is not a channel: each row weighs two, so `CHANNEL` cannot be discharged and
#    `BLACKWELL_GARBLING` has nothing to say.
run() {
  name=$1; from=$2; to=$3
  echo "################ $name" >> "$LOG"
  "$P" "$CASE" "$from" "$to" -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-wrong-value 'val Ignored: String = s"VALUE 8 (8 * 8) 7 $Prior $Rare $Utility = (7:real) / 20"' \
  'val Ignored: String = s"VALUE 8 (8 * 8) 7 $Prior $Rare $Utility = (7:real) / 21"'
run 2-rule-follows-g '$Rare z (8 * s + g) * $Utility a z) 8) 7 = s"' '$Rare z (8 * s + g) * $Utility a z) 8) 7 = g"'
run 3-not-a-channel 'val Forget: String = "(\\t:num. \\i:num. COND (i = NUM_DIV t 8) (1:real) 0)"' \
  'val Forget: String = "(\\t:num. \\i:num. COND (i = NUM_DIV t 8) (2:real) 0)"'

cd "$WT" && git status --porcelain >> "$LOG"
