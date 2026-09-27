#!/bin/sh
# Fire the guards that keep the expander width bound from being empty, card 01520749.
#
# `ExpanderPigeonholeSpec` detaches `RES_GPHP_WIDTH` on the complete graph K(3, 2) at the nineteen-
# step refutation in `ResolutionFixture`, with nothing assumed, and refutes it at w = 20 without
# EXPANDING. `PigeonholeSpec` detaches `RES_PHP_DERIVED_WIDTH` at the same refutation, n = 2. Two
# perturbations:
#
#   1. The hole clause's "every literal is one of the two" conjunct also demands `NUM_LT i ZERO`,
#      in the published `Clause`, so no hole clause with a literal exists. The derivation never
#      reads that conjunct, so the theorem is still proved and published. Expected: red exactly the
#      three tests that derive the inputs, the detachment, the w = 20 control and the r = 0
#      control; green the publication, axiom and resting-on tests, and the narrow-steps test, which
#      reads only data.
#   2. The refutation's seventeenth step names the wrong pivot, (1, 1) where it is (1, 0). The
#      fixture's check of a resolution step must then refuse, since the parent's literal x(1, 0) is
#      neither the pivot nor in the resolvent. Expected: red the detachment and the w = 20 and r = 0
#      controls here, and the n = 2 detachment in `PigeonholeSpec`; green everything else. A checker that
#      accepted it would be a checker that reads nothing.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN: see the card's delivery comment of 2026-09-26, which records this script's run.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/ExpanderPigeonhole.scala
FIXTURE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/ResolutionFixture.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ExpanderPigeonholeSpec garden.xeno.symbolum.theories.PigeonholeSpec'
LOG="$OUT/expander-width.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-a-hole-clause-with-no-literal" >> "$LOG"
"$P" "$SOURCE" \
  '${xv(d, h)}) /\\ s $j i = F) /\\ " +' \
  '${xv(d, h)}) /\\ s $j i = F /\\ NUM_LT i ZERO) /\\ " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-a-hole-clause-with-no-literal" >> "$LOG"

echo "################ 2-a-step-with-the-wrong-pivot" >> "$LOG"
"$P" "$FIXTURE" \
  '17 -> (Vector(pos(1, 1)), (1, 15, (1, 0))),' \
  '17 -> (Vector(pos(1, 1)), (1, 15, (1, 1))),' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-a-step-with-the-wrong-pivot" >> "$LOG"

git status --porcelain -- "$SOURCE" "$FIXTURE" >> "$LOG"
echo "### restore checked" >> "$LOG"
