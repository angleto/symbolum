#!/bin/sh
# Fire card 4bcfc8b9's `COS_POSITIVE`, and through it `PI_HALF_LEAST_ZERO`, at the two things it must not lose.
#
# `CircleSpec` compares each published fact with its text and composes the textbook's sentence, that
# `pi / 2` is the least positive zero of `cos`, from the published facts alone. What it cannot show
# is which premises of the derivation are load-bearing. Two are: the zero of `cos` at `pi / 2`, which
# is what turns "cos falls to its value at pi / 2" into "cos is positive", and the strictness of
# `x < pi / 2`, without which the claim is false at `pi / 2` itself. Both perturbations are
# mathematical rather than structural, so the refusal has to come from `Linarith` deciding that what
# it was handed does not give the goal, not from a term failing to match.
#
# Run on 2026-10-02 over the branch `pi-least-zero` off 7.0 `112fe401`, through the build queue: the
# control green at 8 of 8, and both perturbations aborting the suite with the chain refusing to
# build, each on `LINARITH searched to the end ... so this is decided rather than merely unproved`,
# the first on `real_lt real_zero (cos x)` and the second on `real_lt x (div pi (BIT0 real_one))`.
#
# Expect red on the whole suite both times: the chain is built once and every spec over it aborts,
# which is what a development refusing to construct looks like from a test.
#
# The control is the run before them, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Circle.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CircleSpec'

echo "################ 0-control" >> "$OUT/pi-least-zero.log"
./tools/sbt -batch "$SPEC" >> "$OUT/pi-least-zero.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/pi-least-zero.log"

# 1. The zero at pi / 2 withheld. `cos x` is then known only to be above `cos (pi / 2)`, an atom
# nothing bounds, so `0 < cos x` does not follow.
echo "################ 1-without-the-zero" >> "$OUT/pi-least-zero.log"
"$P" "$SOURCE" \
  'result <- concludeText(Seq(compared, cosHalf), "(0:real) < cos x")' \
  'result <- concludeText(Seq(compared), "(0:real) < cos x")' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/pi-least-zero.log" 2>&1
echo "### exit $? for 1-without-the-zero" >> "$OUT/pi-least-zero.log"

# 2. The bound made non-strict. `COS_DECREASING` wants `x < pi / 2`, and from `x <= pi / 2` that
# does not follow: the point it fails at is `pi / 2`, where `cos` is zero and the claim is false.
echo "################ 2-closed-at-pi-half" >> "$OUT/pi-least-zero.log"
"$P" "$SOURCE" \
  'hT <- proposition("(0:real) <= x /\\ x < pi / 2")' \
  'hT <- proposition("(0:real) <= x /\\ x <= pi / 2")' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/pi-least-zero.log" 2>&1
echo "### exit $? for 2-closed-at-pi-half" >> "$OUT/pi-least-zero.log"

cd "$WT" && git status --porcelain >> "$OUT/pi-least-zero.log"
