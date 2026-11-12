#!/bin/sh
# Put back the defect of card 1e3ef954: `Refutation.counterexample` counting a point where a premise
# is false as a point where the claim was tested, so `{x * x < 0}` with the conclusion `x = 7`
# survives a hundred points at which no premise held.
#
# The perturbation restores the old count exactly: points where every premise held and points where
# one failed go into `Survived` together, and `PremisesNeverHeld` can no longer be reached. What
# should go red is RefutationSpec's test for the card, at its first assertion, and ElaborateSpec's
# report of the `NEVER_HELD` theorem. The control is the run before it, in the same tree, and it
# must be green. Each is a run of its own.
#
# WHAT WAS SEEN, 2026-11-12, on the uncommitted tree that landed this, onto `d47d4901`. Control green
# at 50 tests. Perturbed, 2 of 50 red and no others: RefutationSpec's test for the card at its first
# assertion, "expected PremisesNeverHeld, got Survived(100)", and ElaborateSpec's report reading
# `survived` for `NEVER_HELD` where it wants `premises-never-held`. The restore was verified by the
# tool, and the line it substitutes was present exactly once afterwards.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Refutation.scala
SPECS='tactics/testOnly garden.xeno.symbolum.tactics.RefutationSpec garden.xeno.symbolum.tactics.ElaborateSpec'
LOG="$OUT/refutation-premises.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-premise-false-points-counted" >> "$LOG"
"$P" "$FILE" 'case None if walked.held > 0 => Refutation.Survived(walked.held)' \
  'case None if walked.held + walked.unheld > 0 => Refutation.Survived(walked.held + walked.unheld)' -- \
  ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 1-premise-false-points-counted" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
