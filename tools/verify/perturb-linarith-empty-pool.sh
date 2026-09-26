#!/bin/sh
# Fire the guards that a goal with no hypotheses hears about the empty pool and not the degree, card bacfaba5.
#
# `RefusalSpec` (tactics) and `LinarithSquareBoundarySpec` (theories) assert that a product out of
# reach in a goal with no hypotheses is refused naming the empty pool. The branch is chosen by
# `facts.isEmpty` in `Linarith.naming`; the perturbation makes it never fire, so every such goal
# hears "the hypotheses multiplied reach three" again, which is what the card repaired.
#
# WHAT WAS SEEN, 2026-09-26, at `1bcad72b`, with a hand substitution rather than the tool. Control
# green. Perturbed: `RefusalSpec` red at exactly one test, "should name the empty pool instead, when
# the goal has no hypotheses to multiply", 14 green beside it; `LinarithSquareBoundarySpec` red at
# "should be refused naming the empty pool, on either side of its truth". `LinarithSpec` stayed
# green under the same substitution, so it is not a guard on this branch. Restore verified by
# `git diff --quiet`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Linarith.scala
SPEC_L='theories/testOnly garden.xeno.symbolum.theories.LinarithSquareBoundarySpec'
SPEC_T='tactics/testOnly garden.xeno.symbolum.tactics.RefusalSpec'
LOG="$OUT/linarith-empty-pool.log"
FROM='if LinearForm.obstacleIn(reals, conclusion).isEmpty && facts.isEmpty =>'
TO='if LinearForm.obstacleIn(reals, conclusion).isEmpty && false =>'

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC_L" "$SPEC_T" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The empty-pool branch never fires. Expected: red at the pool test in both specs, run
# separately because a sequenced sbt command stops at the first red.
echo "################ 1-pool-never-empty" >> "$LOG"
"$P" "$SOURCE" "$FROM" "$TO" -- ./tools/sbt -batch "$SPEC_L" >> "$LOG" 2>&1
echo "### exit $? for 1-pool-never-empty, theories" >> "$LOG"
"$P" "$SOURCE" "$FROM" "$TO" -- ./tools/sbt -batch "$SPEC_T" >> "$LOG" 2>&1
echo "### exit $? for 1-pool-never-empty, tactics" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
