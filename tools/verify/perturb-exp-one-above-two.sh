#!/bin/sh
# Fire the derivation of card a714187c's `exp 1 > 2` at two defects it must refuse.
#
# `EXP_ONE_ABOVE_TWO` is published and `TranscendentalSpec` compares every fact of the development
# against the text it is published as, so a derivation that reached a DIFFERENT theorem is caught
# there. What that comparison cannot show is that the two numbers in the argument are load-bearing:
# the index the partial sum is taken at, and the doubling of the geometric term. Both are one
# literal, and both perturbations below are mathematical rather than structural, so the refusal has
# to come from a procedure deciding and not from a term failing to match.
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

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Transcendental.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TranscendentalSpec'

echo "################ 0-control" >> "$OUT/exp-one.log"
./tools/sbt -batch "$SPEC" >> "$OUT/exp-one.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/exp-one.log"

# 1. The partial sum taken one term too early. `Sum f 2` is `1 + 1` and the claim wants five
# halves, so `Linarith` is asked for `5 / 2 <= 2` over numerals and decides it false. The refusal
# is the procedure's: nothing here fails to match.
echo "################ 1-a-term-too-few" >> "$OUT/exp-one.log"
"$P" "$SOURCE" \
  'private val ThirdIndexText: String = "SUC (SUC (SUC (0:num)))"' \
  'private val ThirdIndexText: String = "SUC (SUC (0:num))"' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exp-one.log" 2>&1
echo "### exit $? for 1-a-term-too-few" >> "$OUT/exp-one.log"

# 2. The domination without the doubling. `1 / i!` is not under `(1/2)^i`: at `i = 1` it is one
# against a half, so the schematic with `v <= q` in place of `v <= q + q` is false and `Linarith`
# refuses the schematic itself rather than refusing to apply it.
#
# **The refusal is a budget and not a decision, which is worth knowing before reading the log**:
# it comes back `Linarith.Cubes stopped the search at 33, where it allows 24: this is not evidence
# about ((real_le u) y) either way`, where case 1 comes back decided. A false linear goal over
# numerals is settled; a false one over five atoms with products in it exhausts the schedule
# first. Both are red and only the first says the claim is false.
echo "################ 2-without-the-doubling" >> "$OUT/exp-one.log"
"$P" "$SOURCE" \
  '"p <= 2 * f ==> f * v = 1 ==> v <= q + q")' \
  '"p <= 2 * f ==> f * v = 1 ==> v <= q")' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exp-one.log" 2>&1
echo "### exit $? for 2-without-the-doubling" >> "$OUT/exp-one.log"

cd "$WT" && git status --porcelain >> "$OUT/exp-one.log"
