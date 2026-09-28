#!/bin/sh
# Fire the guard that LINARITH's refusal names an atom no completed square covers, card bacfaba5.
#
# `Linarith.naming` names a square of one unknown only when no other product is out of reach
# (`f62925b6`). The perturbation lets a square be picked first again, by term order, which is the
# code the verification of 2026-09-26 found naming `x * x` for `x * x + y * y >= 2 * (x * y)`.
#
# Expected red, in `LinarithSquareBoundarySpec`: "name the cross term as the obstacle, not a square
# it completed" (round one) and "The atom a refusal names should be one no square covers" (round
# two). Everything else in the file stays green.
#
# WHAT WAS SEEN, 2026-09-27, at the verification branch over `2cb685b7`, with a hand substitution
# rather than the tool: see the card's round-two comment for the red lines. Restore verified by
# `git diff --quiet`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Linarith.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LinarithSquareBoundarySpec'
LOG="$OUT/linarith-square-naming.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. A square may be named first. Expected: red at the two tests named above.
echo "################ 1-square-named-first" >> "$LOG"
"$P" "$SOURCE" \
  'val outOfReach = products.find(atom => !isSquare(atom)).orElse(products.headOption)' \
  'val outOfReach = products.find(atom => !isSquare(atom) || true).orElse(products.headOption)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-square-named-first" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
