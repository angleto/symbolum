#!/bin/sh
# Fire the three index mistakes the sandwich can make and still typecheck, card a714187c.
#
# Both halves compare a partial sum read at one length with one read at another, and every index
# in sight is a `num` — so exchanging two of them is well typed everywhere and changes which
# region of the square is being talked about. Nothing printed can carry that: the statements
# would still be inequalities between sums, and the third of these is a mistake this derivation
# actually made before the suite caught it.
#
# All three are red at the CHAIN, since `Limit` is constructed once. The control is the run
# before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 22 tests, all three red at the chain, restore
# verified clean. Each refusal names what it was HANDED, and the three are worth reading together
# because they are the same shape three times: an index in the wrong place.
#
#   1. `NUM_LE x n`, the true bound `i <= n`, offered where the crossed lemma wants `n <= i`.
#   2. `NUM_LE (NUM_SUB n i) n`, which is `NUM_SUB_LE` and is true, offered where the crossed
#      instance wants `n <= n - i` — the same two terms the other way up.
#   3. `real_le real_zero (a x)`, the non-negativity at the index, offered where the goal is
#      about the SHIFTED index. This is the one of the three that was met rather than imagined:
#      the second half of `SUM_HALVES` reads `a (n + z)` and the first draft asked at `z`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Limit.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LimitSpec'

echo "################ 0-control" >> "$OUT/sandwich.log"
./tools/sbt -batch "$SPEC" >> "$OUT/sandwich.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/sandwich.log"

# 1. The double taken the other way round. `NUM_LE_DOUBLE_SUB` says `n <= (n + n) - i` under
# `i <= n`, and the two arguments are a length and an index; crossed, it asks for
# `i <= (i + i) - n`, which is the claim below the diagonal and is what the bound refuses.
echo "################ 1-the-double-crossed" >> "$OUT/sandwich.log"
"$P" "$SOURCE" \
  'reaches <- rules.specAll(pieces.atMostDouble, List(n, index)).flatMap(rules.mp(_, weak))' \
  'reaches <- rules.specAll(pieces.atMostDouble, List(index, n)).flatMap(rules.mp(_, weak))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/sandwich.log" 2>&1
echo "### exit $? for 1-the-double-crossed" >> "$OUT/sandwich.log"

# 2. The tail compared the other way up. `SUM_GROWS` gives the shorter partial sum under the
# longer, and `NUM_SUB_LE` is what puts `n - i` under `n`; asked at `n` and `n - i` instead it
# wants the longer under the shorter, which is false and which nothing discharges.
echo "################ 2-the-tail-the-wrong-way-up" >> "$OUT/sandwich.log"
"$P" "$SOURCE" \
  'grown <- rules.specAll(ordered, List(shorter, n)).flatMap(rules.mp(_, below))' \
  'grown <- rules.specAll(ordered, List(n, shorter)).flatMap(rules.mp(_, below))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/sandwich.log" 2>&1
echo "### exit $? for 2-the-tail-the-wrong-way-up" >> "$OUT/sandwich.log"

# 3. The non-negativity asked at the index rather than at the SHIFTED index. `SUM_HALVES` puts
# the second half at `n + z`, so the term is `a (n + z)` and not `a z`; this derivation asked at
# `z` first and the chain refused with `0 <= a x` printed against a goal about `a (n + x)`.
# Kept because it is the one of the three that was met rather than imagined.
echo "################ 3-the-shift-forgotten" >> "$OUT/sandwich.log"
"$P" "$SOURCE" \
  'positive <- rules.spec(at, assumedA)' \
  'positive <- rules.spec(index, assumedA)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/sandwich.log" 2>&1
echo "### exit $? for 3-the-shift-forgotten" >> "$OUT/sandwich.log"

cd "$WT" && git status --porcelain >> "$OUT/sandwich.log"
