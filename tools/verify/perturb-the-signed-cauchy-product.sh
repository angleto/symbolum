#!/bin/sh
# Fire the three mistakes the signed argument can make and still typecheck, card a714187c.
#
# The general Cauchy product compares two sums that differ only by magnitudes, so every term in
# sight has the same type as the term it should not be confused with and every index is a `num`.
# The three below are the three joints: which series the non-negative theorem is spent on, which
# stretch the tail bound is asked about, and which of the two gaps is folded back into which side.
#
# All three are red at the CHAIN, since `Limit` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 26 tests, all three red at the chain, restore
# verified clean. Each refusal names what it was HANDED.
#
#   1. `!x. 0 <= abs (a x)`, offered where the instance wants `!x. 0 <= a x`. That is exactly
#      the hypothesis this theorem exists to do without, so the refusal is the general case
#      refusing to collapse into the one under it.
#   2. `NUM_LE (NUM_SUB n i) n`, offered where the collapsed instance wants `NUM_LE n n`. **The
#      comment above this perturbation predicted it would go red later**, on the ground that a
#      bound on `abs (B n - B n)` is true and useless; it goes red at once, at the guard, because
#      `NUM_SUB_LE` is stated at `NUM_SUB` and not at a bare index. The prediction was wrong
#      about where and right about whether, and the line is kept in that form.
#   3. `abs (Sum (\x. a x * (B n - B (n - x))) n) <= ...`, refused by the rewrite for not
#      mentioning the magnitudes` sum. So the two gaps are not interchangeable even though they
#      are two instances of one identity.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/signed-cauchy.log"
./tools/sbt -batch "$SPEC" >> "$OUT/signed-cauchy.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/signed-cauchy.log"

# 1. The non-negative theorem spent on the SIGNED series rather than on the magnitudes. Its
# hypotheses are `!i. 0 <= a i`, which this derivation discharges from `ABS_NONNEG`; handed `a`
# and `b` it wants the terms themselves to be non-negative, which is the hypothesis the general
# theorem exists to do without and which nothing here can produce.
echo "################ 1-spent-on-the-signed-series" >> "$OUT/signed-cauchy.log"
"$P" "$SOURCE" \
  '.specAll(pieces.nonNegativeProduct, List(absA, absB, bigP, bigQ))' \
  '.specAll(pieces.nonNegativeProduct, List(a, b, bigP, bigQ))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/signed-cauchy.log" 2>&1
echo "### exit $? for 1-spent-on-the-signed-series" >> "$OUT/signed-cauchy.log"

# 2. The tail bound asked about the whole prefix rather than about the stretch. `SUM_TAIL_ABS` at
# `(b, NUM_SUB n i, n)` bounds `abs (B n - B (n - i))`, which is the term the gap identity puts
# there; at `(b, n, n)` it bounds `abs (B n - B n)`, which is true, free, and about nothing the
# comparison needs. The guard `NUM_SUB_LE` still discharges, so nothing upstream notices.
echo "################ 2-the-stretch-collapsed" >> "$OUT/signed-cauchy.log"
"$P" "$SOURCE" \
  '.specAll(pieces.stretch, List(b, difference, n))' \
  '.specAll(pieces.stretch, List(b, n, n))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/signed-cauchy.log" 2>&1
echo "### exit $? for 2-the-stretch-collapsed" >> "$OUT/signed-cauchy.log"

# 3. The two gaps folded back the other way round. Both are instances of one identity and both
# are equations between a difference of partial sums and a sum over the gap, so exchanging them
# is well typed everywhere: what it produces is a bound whose two sides are about the magnitudes
# and about the signed terms in the wrong places.
echo "################ 3-the-gaps-exchanged" >> "$OUT/signed-cauchy.log"
"$P" "$SOURCE" \
  'foldedLeft <- Conv
        .sym(signedGap)' \
  'foldedLeft <- Conv
        .sym(magnitudeGap)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/signed-cauchy.log" 2>&1
echo "### exit $? for 3-the-gaps-exchanged" >> "$OUT/signed-cauchy.log"

cd "$WT" && git status --porcelain >> "$OUT/signed-cauchy.log"
