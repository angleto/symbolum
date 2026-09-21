#!/bin/sh
# Fire the three mistakes the addition theorem can make and still typecheck, card a714187c.
#
# Everything in it is a real, and the four existentials it opens are four reals that differ only
# in which series they are the limit of. Exchanging two of them, or reading the convolution at
# the wrong argument, is well typed and produces a theorem about something else.
#
# All three are red at the CHAIN, since `Transcendental` is constructed once. The control is the
# run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 14 tests, all three red at the chain, restore
# verified clean.
#
#   1. `converges (Sum (\i. abs (x^i / i!))) P`, offered where the exchanged instance wants that
#      series to converge to `Q`. The two bounds are not interchangeable even though both are
#      reals and both bound a series of magnitudes.
#   2. The congruence's hypothesis at the wrong argument: what is offered is the convolution of
#      `x` with itself and what is wanted is `x` with `y`. Both are true statements about a
#      convolution, which is the point of the perturbation.
#   3. `transitivity: A * exp y is not B * exp y`, which is the clearest of the three and says
#      exactly what the exchange cost.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Transcendental.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TranscendentalSpec'

echo "################ 0-control" >> "$OUT/addition.log"
./tools/sbt -batch "$SPEC" >> "$OUT/addition.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/addition.log"

# 1. The two absolute limits exchanged in the Cauchy product. `P` and `Q` are both reals and both
# are the limit of a series of magnitudes, so the swap typechecks; what it asks for is that the
# magnitudes of `x`'s terms converge to `y`'s bound.
echo "################ 1-the-two-bounds-exchanged" >> "$OUT/addition.log"
"$P" "$SOURCE" \
  '.flatMap(rules.specAll(_, List(termsX, termsY, a, b, p, q)))' \
  '.flatMap(rules.specAll(_, List(termsX, termsY, a, b, q, p)))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/addition.log" 2>&1
echo "### exit $? for 1-the-two-bounds-exchanged" >> "$OUT/addition.log"

# 2. The convolution read at `x` twice. `EXP_CONVOLUTION` is about the terms at two arguments and
# both are reals, so this is a true statement about the square of one series and has nothing to
# do with the product the Cauchy step produced.
echo "################ 2-the-convolution-at-one-argument" >> "$OUT/addition.log"
"$P" "$SOURCE" \
  'pointwise <- rules.specAll(convolution, List(x, y, k)).flatMap(rules.gen(k, _))' \
  'pointwise <- rules.specAll(convolution, List(x, x, k)).flatMap(rules.gen(k, _))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/addition.log" 2>&1
echo "### exit $? for 2-the-convolution-at-one-argument" >> "$OUT/addition.log"

# 3. The two values exchanged when the product is assembled. `A` and `B` are both reals and the
# congruence is happy with either order, so what comes out is `exp x * exp y = B * A`, which is
# true of nothing the rest of the derivation proved.
echo "################ 3-the-two-values-exchanged" >> "$OUT/addition.log"
"$P" "$SOURCE" \
  'byValue <- LogicError.lift(Term.app(times, a))' \
  'byValue <- LogicError.lift(Term.app(times, b))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/addition.log" 2>&1
echo "### exit $? for 3-the-two-values-exchanged" >> "$OUT/addition.log"

cd "$WT" && git status --porcelain >> "$OUT/addition.log"
