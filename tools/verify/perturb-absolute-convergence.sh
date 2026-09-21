#!/bin/sh
# Fire the three steps that carry the absolute convergence theorem, card a714187c.
#
# The statement is one line and the proof is an identity: `f i` is `(f i + abs (f i)) - abs (f i)`.
# What makes that work is three things the statement cannot say — that the bracket's two bounds
# come from the two DIFFERENT halves of `abs`, that the hypothesis becomes a bound through the
# sequence's own terms, and that the sequence `CONVERGES_ADD` produces is a redex which has to be
# reduced before it can be identified with `Sum f`.
#
# All three are red at the CHAIN, since `Limit` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# A FOURTH WAS TRIED AND DID NOT FIRE, and it is worth more than the three that did. The sequence
# `CONVERGES_ADD` hands back carries a beta redex, and this derivation reduced it on the strength
# of a sentence about `LimitSpec`'s composition test rather than of a measurement. Removing the
# reduction left the whole suite green: the redex is real, `Conv.betaNormalise` moves the term,
# and **nothing downstream reads that sequence**. So the call was deleted rather than kept with
# prose beside it, and there is no perturbation here for a step that is not there. The
# difference from the composition test is that its redex reaches an assertion and this one does
# not.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this. Control green at 20 tests, all three
# red at the chain, restore verified clean. Each refusal names what it was handed:
#
#   1. `real_le (f i) (abs (f i))`, which is the UPPER bound offered where the lower one is
#      wanted. Both are true and only one makes the bracket non-negative.
#   2. `converges (Sum (\x. abs (f x))) l`, the hypothesis itself, offered where the crossed
#      lemma wants every term of the sequence above `l`.
#   3. The whole `!x. NUM_LE ZERO x ==> ...` obligation printed out, with the absolute partial
#      sum added twice on each side where the reduced form has it nowhere. The identity is the
#      proof and a sign in it is not a detail.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/absolute.log"
./tools/sbt -batch "$SPEC" >> "$OUT/absolute.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/absolute.log"

# 1. The lower bound taken from the wrong half of `abs`. `ABS_ABOVE` says `x <= abs x` and
# `ABS_ABOVE_NEG` says `-x <= abs x`, and only the second makes `f i + abs (f i)` non-negative:
# the first gives `f i <= abs (f i)`, which is what the UPPER bound is for and says nothing about
# the sign of the bracket. The two are used once each and crossing them leaves the comparison
# test without the one hypothesis it cannot do without.
echo "################ 1-the-lower-bound-from-the-wrong-half" >> "$OUT/absolute.log"
"$P" "$SOURCE" \
  '.spec(atI, bounds.aboveNegation)' \
  '.spec(atI, bounds.above)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/absolute.log" 2>&1
echo "### exit $? for 1-the-lower-bound-from-the-wrong-half" >> "$OUT/absolute.log"

# 2. The bound asked about the limit instead of about a term. `CONVERGES_GE` turns "increasing
# and convergent to `l`" into "at most `l`" by putting one of the sequence's OWN terms under the
# limit; asked the other way round it wants every term above `l`, which is the claim that fails
# and is what the lemma's own docstring says is false below that term's index.
echo "################ 2-the-bound-the-wrong-way-up" >> "$OUT/absolute.log"
"$P" "$SOURCE" \
  '.specAll(pieces.aboveBound, List(absSeries, l, here, n))' \
  '.specAll(pieces.aboveBound, List(absSeries, here, l, n))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/absolute.log" 2>&1
echo "### exit $? for 2-the-bound-the-wrong-way-up" >> "$OUT/absolute.log"

# 3. The identity written with the wrong sign. `f i` is `(f i + abs (f i)) - abs (f i)`, and the
# whole proof is that one line: the bracket is what the comparison test settles and the absolute
# series is what is taken off again. Written as a sum rather than a difference the algebra is
# still true of something, and what fails is the identification of the two sequences.
echo "################ 3-the-identity-with-the-wrong-sign" >> "$OUT/absolute.log"
"$P" "$SOURCE" \
  '"!p:real. !q:real. !r:real. p = q + r ==> p + -r = q"' \
  '"!p:real. !q:real. !r:real. p = q + r ==> p + -r + r + r = q + r + r"' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/absolute.log" 2>&1
echo "### exit $? for 3-the-identity-with-the-wrong-sign" >> "$OUT/absolute.log"

cd "$WT" && git status --porcelain >> "$OUT/absolute.log"
