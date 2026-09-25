#!/bin/sh
# Fire the rationals' density and Archimedes at the one choice each argument makes, card 6a183162.
#
# 1. Density's witness is the midpoint `(x + y) * RAT_INV 2`. Dropping the halving makes it
#    `x + y`, which lies between `x` and `y` for no pair in general, and the construction must
#    refuse: doubling it no longer gives `x + y`, and the ring says so.
# 2. Archimedes bounds a negative numerator `-m` by `RAT_OF_NUM 0`, since `0 <= m` shifted by `-m`
#    is the cross-multiplied order there. Bounding it by `RAT_OF_NUM m` instead keeps a true
#    statement but not this argument: the right-hand side the proof is aimed at is then `m * D`, and
#    the equation that closes it, which reads `O = 0`, cannot reach it.
#
# FractionSpec is the spec: every fact is derived inside `Fraction.construct`, so a refusal aborts
# the suite at construction, which is the red this expects. The control before must be green.
# Each target was counted before it was run and occurs once in `Density.scala`, which is what the
# harness beside this one learned the hard way.
#
# WHAT WAS SEEN, 2026-09-25: control green at 16 tests. Perturbed, 1 aborted construction at the
# midpoint's equation, the ring finding `x + x + y + y` where the doubled midpoint should have read
# `x + y`, and 2 aborted it at the negative case's closing equation, `INT_ZERO` against
# `m * D - 0 * D`. Each is the refusal predicted above. Restore verified by the tool after each.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Density.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.FractionSpec'
LOG="$OUT/rational-density.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-midpoint-not-halved" >> "$LOG"
"$P" "$SOURCE" \
  'middle <- moves.times(sum, half)' \
  'middle <- moves.times(sum, v.one)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-midpoint-not-halved" >> "$LOG"

echo "################ 2-the-negative-bound-is-m" >> "$LOG"
"$P" "$SOURCE" \
  'bound = if (negative) v.natZero else m' \
  'bound = if (negative) m else m' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-negative-bound-is-m" >> "$LOG"
