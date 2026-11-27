#!/bin/sh
# Fire the guards of the summary facts of Decision (no card: asked by Angelo on 2026-11-27 for T4 of
# the essay in `thinktank/utitlita_e_danno`, "a faithful summary of the frame is the frame").
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own, because one refusal stops the chain from being built and every later fact with it.
#
# WHAT WAS SEEN, 2026-11-27, on the tree of 338482fe. Control green (DecisionSpec 12); every
# perturbation aborts the suite because the chain does not build, restores verified, tree as before.
#
#   1, 2, 4, 5. Refused by the check of each fact against its text: the derivation proves the
#      statement as written before the edit and the text now says something else ("expected an
#      instance of", or "whether ... is an instance of"). These show that the proved fact is the
#      written one; they are not arithmetic refusing a false claim, since the proofs are written
#      against the true statements.
#   3. Refused by Linarith, decided: "searched to the end: no non-negative combination of the
#      hypotheses gives" the strict goal.
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
LOG="$OUT/decision-summary.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. ARGMAX_SCALE at c = 0 allowed: false, since `\a. 0 * f a` is constant and its first maximiser
#    is 0 while `f`'s need not be.
# 2. SUFFICIENT_SUMMARY_UTILITY without `0 <= w s`: false, since a negative weight reverses the
#    order of the actions at that signal and the summary reader plays the worst one.
# 3. SUMMARY_NO_FREE_CURE's last step asked strictly below zero: false at the summary that forgets
#    nothing, and Linarith must refuse a strict goal from non-strict facts.
# 4. BAYES_RULE_OPTIMAL for a rule allowed one action beyond `top`: false, since that action can pay
#    more than every action the Bayes rule chooses among.
# 5. SUMMARY_READER_VALUE against a summary channel whose rows weigh two: not a channel, and its
#    value is twice the one collected.
run() {
  name=$1; from=$2; to=$3
  echo "################ $name" >> "$LOG"
  "$P" "$DECISION" "$from" "$to" -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-scale-by-zero \
  '0 < c ==> Argmax (\\a:num. c * f a) n = Argmax f n' \
  '0 <= c ==> Argmax (\\a:num. c * f a) n = Argmax f n'
run 2-weight-of-any-sign \
  '"!f:num->num. !w:num->real. !N:num->bool. (!s:num. s < m ==> 0 <= w s) ==> "' \
  '"!f:num->num. !w:num->real. !N:num->bool. "'
run 3-cure-strictly \
  '(${onHalf("~N", DF)} - ${onHalf("~N", DK)}) <= 0")' \
  '(${onHalf("~N", DF)} - ${onHalf("~N", DK)}) < 0")'
run 4-rule-beyond-top \
  '"(!s:num. s < m ==> d s <= top) ==> "' \
  '"(!s:num. s < m ==> d s <= top + 1) ==> "'
run 5-reader-rows-weigh-two \
  '(\\y:num. \\t:num. Sum (\\s:num. k y s * COND (f s = t) (1:real) 0) m) u")' \
  '(\\y:num. \\t:num. Sum (\\s:num. k y s * COND (f s = t) (2:real) 0) m) u")'

cd "$WT" && git status --porcelain >> "$LOG"
