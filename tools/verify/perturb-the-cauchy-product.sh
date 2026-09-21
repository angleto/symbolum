#!/bin/sh
# Fire the three mistakes the squeeze can make and still typecheck, card a714187c.
#
# The Cauchy product is a bracket, and every term in it is a real and every index a `num`, so
# the three ways of getting a bracket wrong — comparing terms with partial sums, taking the
# sandwich half that points the other way, and dropping the doubling — are all well typed and
# all change what is being asserted. Nothing printed carries any of them: what comes out in each
# case is still an inequality between sums, and the first is a mistake this derivation actually
# made before the chain caught it.
#
# All three are red at the CHAIN, since `Limit` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 24 tests, all three red at the chain, restore
# verified clean. Each refusal names what it was HANDED, and reading the three together is the
# point: the same bracket got wrong in the three places a bracket can be got wrong.
#
#   1. `!x. Sum c x <= Sum c x`, the reflexivity at the PARTIAL SUMS, offered where the
#      comparison test wants it at the terms. This is the one of the three that was met rather
#      than imagined.
#   2. `Sum c n <= Sum a n * Sum b n`, which is the other half of the sandwich and is true,
#      offered where the argument wants the square underneath.
#   3. `Sum c n <= l`, the bound read at `n`, offered where the transitivity wants it at
#      `n + n`. So the doubling is load-bearing, which is what the name's docstring claims.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/cauchy-product.log"
./tools/sbt -batch "$SPEC" >> "$OUT/cauchy-product.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/cauchy-product.log"

# 1. The series dominating itself, asserted at its PARTIAL SUMS rather than at its terms. The
# comparison test compares `f n` with `g n`, and the `n`th term of the convolution is a whole
# inner sum; `Sum c n` is the `n`th partial sum of that, which is a different real and reflexive
# just as truly. Kept because it is the one of the three that was met rather than imagined: the
# chain refused with `!x. Sum c x <= Sum c x` printed against a goal about the terms.
echo "################ 1-reflexive-at-the-partial-sum" >> "$OUT/cauchy-product.log"
"$P" "$SOURCE" \
  '.flatMap(rules.spec(termAt, _))
        .flatMap(rules.gen(k, _))' \
  '.flatMap(rules.spec(cauchyAt, _))
        .flatMap(rules.gen(n, _))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cauchy-product.log" 2>&1
echo "### exit $? for 1-reflexive-at-the-partial-sum" >> "$OUT/cauchy-product.log"

# 2. The other half of the sandwich, where the argument needs this one. `A * B <= l` comes from
# `P n <= D (n + n)`, which is `SUM_SQUARE_BELOW_CAUCHY`; `SUM_CAUCHY_BELOW_SQUARE` is the half
# that points the other way, is equally true, and is already spent five lines up. Swapped in
# here it gives `D n <= P n` where the chain wants the square underneath.
echo "################ 2-the-half-that-points-back" >> "$OUT/cauchy-product.log"
"$P" "$SOURCE" \
  'squareBelowDouble <- rules
        .specAll(pieces.squareBelowCauchy, List(a, b, n))' \
  'squareBelowDouble <- rules
        .specAll(pieces.cauchyBelowSquare, List(a, b, n))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cauchy-product.log" 2>&1
echo "### exit $? for 2-the-half-that-points-back" >> "$OUT/cauchy-product.log"

# 3. The doubling dropped. `SUM_SQUARE_BELOW_CAUCHY` puts the square under the convolution read
# at `n + n`, and reading the bound off at `n` instead is the whole of what the sandwich buys:
# `P n <= D n` is FALSE, and what refuses it is the chain being handed `Sum c (n + n) <= l`
# where the transitivity wants `Sum c n <= l`. This is the perturbation that says the doubling
# is load-bearing rather than a spelling, which is the claim the name's docstring makes.
echo "################ 3-the-doubling-dropped" >> "$OUT/cauchy-product.log"
"$P" "$SOURCE" \
  '.spec(doubled, cauchyBelowLimit)' \
  '.spec(n, cauchyBelowLimit)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cauchy-product.log" 2>&1
echo "### exit $? for 3-the-doubling-dropped" >> "$OUT/cauchy-product.log"

cd "$WT" && git status --porcelain >> "$OUT/cauchy-product.log"
