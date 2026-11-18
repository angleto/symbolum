#!/bin/sh
# Fire the guards of BLACKWELL_FILTER, LECAM_VALUE, LECAM_BOUND and LECAM_OVERLAP (no card: asked by
# Angelo on 2026-11-18 for the essay in `thinktank/utitlita_e_danno`, recorded in docs/adr/0063).
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own, because one refusal stops the chain from being built and every later fact with it.
#
# WHAT WAS SEEN, 2026-11-18, on the tree that landed this. Control green (DecisionSpec 10); every
# perturbation aborts the suite because the chain does not build, restores verified, tree as before.
#
#   1. Refused by the check of each fact against its text: the derivation proves the statement with
#      weight one and the text says two. The filter's proof is written against the true garbling, so
#      this is a mismatch and not arithmetic refusing a claim.
#   2. Refused by Linarith, decided: no non-negative combination of the hypotheses gives the goal.
#   3. Refused by Linarith on its fragment: the claim is a product of two unknowns beyond the degree
#      the hypotheses reach. A refusal, not a counterexample.
#   4. Refused by Linarith on its budget, which says of itself that this is not evidence either way.
#
# READ THE LOG, NOT THE EXIT CODE: `testOnly` over an aborted suite exited 0 in runs 1, 2 and 4 and
# 1 in run 3. `*** 1 SUITE ABORTED ***` and the refusal under it are the reading.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DECISION=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Decision.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DecisionSpec'
LOG="$OUT/decision-lecam.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. A filter whose rows weigh two: not a channel, and the value it states can exceed the original.
# 2. The value of the two-point problem with the overlap added rather than subtracted, in the goal
#    the derivation closes: the arithmetic must refuse it.
# 3. The bound with `max a b` for `min a b`: false (a = 1, b = 0, P = Q).
# 4. The overlap as one less a third of the L1 distance rather than a half.
run() {
  name=$1; from=$2; to=$3
  echo "################ $name" >> "$LOG"
  "$P" "$DECISION" "$from" "$to" -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-filter-weighs-two \
  '"VALUE n r top prior (\\y:num. \\t:num. Sum (\\s:num. k y s * COND (f s = t) (1:real) 0) m) u <= " +' \
  '"VALUE n r top prior (\\y:num. \\t:num. Sum (\\s:num. k y s * COND (f s = t) (2:real) 0) m) u <= " +'
run 2-value-adds-the-overlap \
  's"VALUE 2 $Mn 1 $Prior $Rows $Pay = $Ph * $Gn - Sum' \
  's"VALUE 2 $Mn 1 $Prior $Rows $Pay = $Ph * $Gn + Sum'
run 3-bound-with-max \
  '"min a b * Sum (\\s:num. min (P s) (Q s)) m <= Sum (\\s:num. min (a * P s) (b * Q s)) m"' \
  '"max a b * Sum (\\s:num. min (P s) (Q s)) m <= Sum (\\s:num. min (a * P s) (b * Q s)) m"'
run 4-overlap-a-third \
  '"Sum (\\s:num. min (P s) (Q s)) m = 1 - Sum (\\s:num. abs (P s - Q s)) m / 2"' \
  '"Sum (\\s:num. min (P s) (Q s)) m = 1 - Sum (\\s:num. abs (P s - Q s)) m / 3"'

cd "$WT" && git status --porcelain >> "$LOG"
