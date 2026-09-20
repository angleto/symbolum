#!/bin/sh
# Fire the three places `NUM_CHOOSE` can be wrong and still look right, card a714187c.
#
# A binomial coefficient is a recursion whose every entry is a number nobody reads: the three
# published facts are what a reader checks, and each of them stays PROVABLE under a definition
# that computes something else. `PeanoSpec` guards that by computing `4 choose 2` and asking for
# six; these three show what that guard is guarding, by making the tree wrong in the three ways
# it can be made wrong without the statements changing shape.
#
# The third is not about the mathematics at all. It is the defect this stage actually hit: the
# `COND` facts quantify their branches at `'a`, so specialising one at a number without
# instantiating the type first refuses with a message that reads as a fault in the recursion.
#
# All three are red at the CHAIN, since `Peano` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-20, on the tree that landed this. Control green at 32 tests, all three
# red at the chain, restore verified clean. Each refusal names a different guard, which is the
# half worth reading:
#
#   1. `expected NUM_CHOOSE_SUC as it is written, found ... NUM_CHOOSE x (SUC y) + NUM_CHOOSE x
#      (SUC y)`. The doubled entry, caught by the comparison against the written statement and
#      not by anything about the recursion, which built perfectly well.
#   2. `expected the goal the driver opened, found NUM_CHOOSE ZERO ZERO = ZERO`. The base row
#      crossed, caught in the induction's own base before any statement is compared.
#   3. `application: expected a, found num`. The type variable, caught in the kernel, and the
#      message names neither `COND_TRUE` nor the caller. That is the whole reason this one is in
#      the harness: it is what the defect looks like from outside, and it looks like a fault in
#      the recursion.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Peano.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.PeanoSpec'

echo "################ 0-control" >> "$OUT/pascal.log"
./tools/sbt -batch "$SPEC" >> "$OUT/pascal.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/pascal.log"

# 1. The predecessor dropped from the step, which is the off-by-one the whole shape exists to
# avoid: `C(n+1, k+1)` becomes `C(n, k+1) + C(n, k+1)` and every entry doubles down the triangle.
# Nothing about the definition is ill-formed and the recursion still builds; what refuses is the
# comparison against the written Pascal's rule, which is what `checked` is for.
echo "################ 1-the-predecessor-dropped" >> "$OUT/pascal.log"
"$P" "$SOURCE" \
  '"COND (k = ZERO) (SUC ZERO) (NUM_ADD (v (PRE k)) (v k))",' \
  '"COND (k = ZERO) (SUC ZERO) (NUM_ADD (v k) (v k))",' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/pascal.log" 2>&1
echo "### exit $? for 1-the-predecessor-dropped" >> "$OUT/pascal.log"

# 2. The base row's two branches crossed, so `C(0, 0)` is zero and `C(0, k+1)` is one. The whole
# triangle is then zero, which is a perfectly good recursion and satisfies no statement here.
echo "################ 2-the-base-row-crossed" >> "$OUT/pascal.log"
"$P" "$SOURCE" \
  '"\\k:num. COND (k = ZERO) (SUC ZERO) ZERO",' \
  '"\\k:num. COND (k = ZERO) ZERO (SUC ZERO)",' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/pascal.log" 2>&1
echo "### exit $? for 2-the-base-row-crossed" >> "$OUT/pascal.log"

# 3. The type instantiation of `COND_TRUE` dropped. This is the one that is not about binomials:
# the fact quantifies its branches at `'a` and specialising it at a number without instantiating
# first refuses inside the kernel's application check, with a message naming the type variable
# and not the caller.
echo "################ 3-the-conditional-not-instantiated" >> "$OUT/pascal.log"
"$P" "$SOURCE" \
  '        .fact(Classical.CondTrue)
        .map(Kernel.instType(Map("a" -> numbers), _))' \
  '        .fact(Classical.CondTrue)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/pascal.log" 2>&1
echo "### exit $? for 3-the-conditional-not-instantiated" >> "$OUT/pascal.log"

cd "$WT" && git status --porcelain >> "$OUT/pascal.log"
