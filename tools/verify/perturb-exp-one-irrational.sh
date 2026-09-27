#!/bin/sh
# Fire the derivation of card fe0e59ed's `EXP_ONE_IRRATIONAL` at the two bounds it must not lose.
#
# `TranscendentalSpec` compares the published fact with its text and asserts what it rests on, so a
# derivation that reached a different theorem, or the same one by another route, is caught there.
# What neither can show is that the two numbers the argument turns on are load-bearing: the doubling
# in the tail bound, and the margin that makes the last inequality strict. Both perturbations are
# mathematical rather than structural, so the refusal has to come from `Linarith` deciding a claim
# false, not from a term failing to match.
#
# Seen on 2026-09-27, before this file was run under sbt, through a scala-cli probe over the classes
# of 7a15f023 with the perturbed `Fourier.scala` compiled beside them: both came back with
# `LINARITH searched to the end ... so this is decided rather than merely unproved`, the first on
# `real_mul (real_of_num (NUM_FACT (SUC q))) e < ... + real_one`, the second on
# `Sum f (SUC (SUC q) + n) <= Sum f (SUC (SUC q)) + f (SUC (SUC q))`. The first perturbation tried
# was `B = Q`, running the argument at the ratio's own denominator; it was refused STRUCTURALLY, by
# the divisibility step being handed a proof of `q <= SUC q`, and is not kept for that reason.
#
# Run under sbt the same day, over the tree of 6c80b4e0: the control green at 23 of 23, and both
# perturbations aborting the suite with the chain refusing to build on the two refusals above.
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

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Fourier.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TranscendentalSpec'

echo "################ 0-control" >> "$OUT/exp-one-irrational.log"
./tools/sbt -batch "$SPEC" >> "$OUT/exp-one-irrational.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/exp-one-irrational.log"

# 1. The margin taken away. From `3 <= q + 2` the derivation gets `3 * (b! * f (b + 1)) <= 1`,
# and the upper bound on `b! * exp 1` is then under the natural below it plus two thirds. Weakened
# to `2 * ... <= 1`, which is still true, it is under that natural plus one, and the step asking for
# strictly less no longer follows from what it is handed, since those facts allow equality: the
# refusal is the strict inequality's and nobody else's.
echo "################ 1-without-the-margin" >> "$OUT/exp-one-irrational.log"
"$P" "$SOURCE" \
  'small <- settle(s"3 * ($factorial * $term) <= 1"' \
  'small <- settle(s"2 * ($factorial * $term) <= 1"' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exp-one-irrational.log" 2>&1
echo "### exit $? for 1-without-the-margin" >> "$OUT/exp-one-irrational.log"

# 2. The tail bound without its doubling. What that step is handed bounds the partial sums past
# `b + 1` by `S + 2 * f (b + 1)`, which is what a geometric series of ratio one half sums to, and the
# claim with the doubling removed does not follow from it: the bound itself is refused.
echo "################ 2-without-the-doubling" >> "$OUT/exp-one-irrational.log"
"$P" "$SOURCE" \
  'settle(s"Sum $F ($N0 + $n) <= Sum $F ($N0) + 2 * $F ($N0)",' \
  'settle(s"Sum $F ($N0 + $n) <= Sum $F ($N0) + $F ($N0)",' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exp-one-irrational.log" 2>&1
echo "### exit $? for 2-without-the-doubling" >> "$OUT/exp-one-irrational.log"

cd "$WT" && git status --porcelain >> "$OUT/exp-one-irrational.log"
