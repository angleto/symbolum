#!/bin/sh
# Fire the guard that a series value holding a reciprocal nothing places is not a decision, card d3fd8018.
#
# `Convergence.numeric` counts `inv t` and `s / t` as a number only where LINARITH proves `t`
# strictly positive or strictly negative (`apart`). The perturbation makes every reciprocal and
# every divisor count as placed, which is the code before `ba68dcbc`, keeping `apart` referenced so
# that an unused-member warning under -Xfatal-warnings cannot be what goes red.
#
# Expected red, in `SeriesFragmentBoundarySpec`: "A value whose truth the theory leaves open" (the
# case round one found, `2 + inv 0`) and "A value that is 2 once a reciprocal of nought is read"
# (its neighbours, added by round two). Everything else in the file stays green, the controls
# "stay a decision" and "still be a decision" among them.
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

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Convergence.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesFragmentBoundarySpec'
LOG="$OUT/series-divisor-apart.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Every reciprocal counts as placed. Expected: red at the two tests named above.
echo "################ 1-every-reciprocal-placed" >> "$LOG"
"$P" "$SOURCE" \
  'case App(Const(Real.Inverse, _), argument) => numeric(argument) && apart(argument)' \
  'case App(Const(Real.Inverse, _), argument) => numeric(argument) && (apart(argument) || true)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-every-reciprocal-placed" >> "$LOG"

# 2. Every divisor counts as placed. Expected: red at the neighbours' test only, on `1 / 0` and
# `3 / (1 - 1)`, since the case of round one is written with `inv`.
echo "################ 2-every-divisor-placed" >> "$LOG"
"$P" "$SOURCE" \
  'numeric(dividend) && numeric(divisor) && apart(divisor)' \
  'numeric(dividend) && numeric(divisor) && (apart(divisor) || true)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-every-divisor-placed" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
