#!/bin/sh
# Fire the three mistakes the split can make and still typecheck, card a714187c.
#
# The exponential's absolute convergence is a split: a head up to an index and a geometric tail
# past it. Every index in sight is a `num` and every bound a real, so exchanging the two halves
# of the split, or taking the index from the wrong quantity, is well typed and changes what is
# being asserted. Nothing printed carries that.
#
# All three are red at the CHAIN, since `Transcendental` is constructed once. The control is the
# run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 12 tests, all three red at the chain, restore
# verified clean.
#
#   1. `2 * abs x <= real_of_num (NUM_CEIL (2 * abs x))`, offered where the undoubled instance
#      wants the ceiling of `abs x`. So the factor two is load-bearing: it is what makes the
#      ratio a half rather than merely something under one.
#   2. **`n occurs free in 2 of the hypotheses`**, and the comment above this perturbation
#      predicted `disjElim` would accept the exchange and something later would notice. It is
#      `disjElim` that notices, but not by comparing conclusions: handed the cases the wrong way
#      round it discharges the wrong disjunct from each, both survive as hypotheses, and the
#      `gen n` after it refuses by naming them. Right about whether, wrong about where, and the
#      line is kept in that form.
#   3. `2 * abs x <= real_of_num (SUC (m + j))`, offered where the off-by-one instance wants the
#      successor of that again. The induction hands the halving its inner index and no other.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Transcendental.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TranscendentalSpec'

echo "################ 0-control" >> "$OUT/exponential.log"
./tools/sbt -batch "$SPEC" >> "$OUT/exponential.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/exponential.log"

# 1. The index taken from `abs x` rather than from `2 * abs x`. `NUM_CEIL_LE` answers for
# whatever it is given, so the ceiling of the magnitude alone is a natural number and the bound
# it satisfies is `abs x <= real_of_num M`. The halving needs twice that, and it is the factor
# two that makes the ratio a half rather than merely less than one.
echo "################ 1-the-index-not-doubled" >> "$OUT/exponential.log"
"$P" "$SOURCE" \
  'val ceilingText = "NUM_CEIL (2 * abs (x:real))"' \
  'val ceilingText = "NUM_CEIL (abs (x:real))"' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exponential.log" 2>&1
echo "### exit $? for 1-the-index-not-doubled" >> "$OUT/exponential.log"

# 2. The two cases of the split exchanged. Both prove the same conclusion, so `disjElim` is
# happy to take either in either slot; what is not the same is which disjunct each carries as a
# hypothesis, and `NUM_LE_TOTAL` at `(n, M)` fixes that order.
echo "################ 2-the-cases-exchanged" >> "$OUT/exponential.log"
"$P" "$SOURCE" \
  '.disjElim(total, beforeTheIndex, afterTheIndex)' \
  '.disjElim(total, afterTheIndex, beforeTheIndex)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exponential.log" 2>&1
echo "### exit $? for 2-the-cases-exchanged" >> "$OUT/exponential.log"

# 3. The halving asked at the index rather than at its successor. `EXP_TERM_HALVES` is stated
# with `SUC i` on both the bound and the term, and the induction hands it the inner index; handed
# the successor instead it is a true instance about the step after the one being taken.
echo "################ 3-the-halving-off-by-one" >> "$OUT/exponential.log"
"$P" "$SOURCE" \
  '.specAll(halving, List(x, inner))' \
  '.specAll(halving, List(x, successorOfInner))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/exponential.log" 2>&1
echo "### exit $? for 3-the-halving-off-by-one" >> "$OUT/exponential.log"

cd "$WT" && git status --porcelain >> "$OUT/exponential.log"
