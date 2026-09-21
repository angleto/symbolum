#!/bin/sh
# Fire the two steps that keep the tail facts off a Cauchy criterion, card a714187c.
#
# Both facts are short and both rest on one move that the statement cannot show. `SUM_BELOW_LIMIT`
# turns a convergence into a bound by putting one of the sequence's OWN terms under the limit,
# which is the only direction that works and is false below that term's index. `CONVERGES_TAIL`
# gets its value by a congruence on the convergence's SECOND argument, which is what keeps the
# sequence out of the way until the end.
#
# Between them they are why this development still has no Cauchy criterion: for a series of
# non-negative terms the tail from `N` on is at most `l - Sum f N`, so the criterion's content is
# reachable without the criterion.
#
# Both are red at the CHAIN, since `Limit` is constructed once. The control is the run before
# them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this. Control green at 21 tests, both red at
# the chain, restore verified clean. Both refusals name what was HANDED rather than what failed:
#
#   1. `converges (Sum f) l`, the hypothesis itself, offered where the crossed lemma asks for
#      every term of the sequence to be above `l`.
#   2. `converges (\x. l) l`, the constant sequence, offered where the crossed instance asks for
#      the negated partial sums to converge to `l`. The two sequences are the same shape to a
#      reader and carry different values, which is why exchanging them type-checks.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/tail.log"
./tools/sbt -batch "$SPEC" >> "$OUT/tail.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/tail.log"

# 1. The bound asked the wrong way up. `CONVERGES_GE` puts a term under the limit and is what
# turns "increasing and convergent to `l`" into "at most `l`"; crossed, it asks for every term
# of the sequence to be above `l`, which is the claim that fails and is what makes this the one
# direction that works.
echo "################ 1-the-bound-the-wrong-way-up" >> "$OUT/tail.log"
"$P" "$SOURCE" \
  '.specAll(aboveBound, List(partial, l, here, n))' \
  '.specAll(aboveBound, List(partial, here, l, n))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/tail.log" 2>&1
echo "### exit $? for 1-the-bound-the-wrong-way-up" >> "$OUT/tail.log"

# 2. The two sequences added the other way round. `CONVERGES_ADD` is told which sequence carries
# which value, and here one is the constant `l` and the other the negated partial sums: crossed,
# the values no longer match the sequences and the second modus ponens has nothing to accept.
echo "################ 2-the-two-sequences-crossed" >> "$OUT/tail.log"
"$P" "$SOURCE" \
  '.specAll(added, List(steadyParts._1, turnedParts._1, l, turnedParts._2))' \
  '.specAll(added, List(turnedParts._1, steadyParts._1, l, turnedParts._2))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/tail.log" 2>&1
echo "### exit $? for 2-the-two-sequences-crossed" >> "$OUT/tail.log"

cd "$WT" && git status --porcelain >> "$OUT/tail.log"
