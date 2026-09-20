#!/bin/sh
# Fire the cancellation of card fa8737ad at the two things it rests on, `docs/adr/0036`.
#
# `INT_MUL_CANCEL_NUM` is the restricted law: the factor it cancels is `INT_OF_NUM (SUC d)` and not
# an arbitrary non-zero integer, and the whole argument of the record is that the successor is what
# makes the rationals' carrier need no carving. `IntegerSpec` compares the published statement and
# spends it at a numeral; what it cannot show is that the successor is **load-bearing** rather than
# decorative, nor that the two sides of the rearrangement are matched to the right halves.
#
# Both perturbations are red at the chain: `Integer` is built once, so a step that does not close
# makes the development refuse and every spec over it aborts.
#
# The control is the run before them, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Integer.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.IntegerSpec'

echo "################ 0-control" >> "$OUT/cancelling.log"
./tools/sbt -batch "$SPEC" >> "$OUT/cancelling.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/cancelling.log"

# 1. The multiplier is no longer a successor, so the claim being cancelled is FALSE at `d = 0`.
#
# **What refuses is not what this comment first predicted, and the difference is worth keeping.**
# The prediction was the positivity: `NUM_ZERO_LT_SUC` gives `0 < SUC d` where
# `NUM_MUL_CANCEL_LEFT` at this multiplier wants `0 < d`. What actually happens is earlier and
# louder: the rules that fold the multiplier into a pair are built by unfolding the embedding at
# `SUC d`, so with the premise written at `d` nothing fires and `eqMp` refuses, naming the class
# of the built pair against the unfolded premise. So this case shows that the shape of the
# multiplier is threaded through the whole derivation rather than assumed once, and it does NOT
# isolate the positivity step. Isolating that one would need a multiplier that folds and is not
# positive, which is a term this construction cannot produce.
echo "################ 1-the-multiplier-is-not-a-successor" >> "$OUT/cancelling.log"
"$P" "$SOURCE" \
  'multiplier <- Parser.term(theory, notation, "INT_OF_NUM (SUC (d:num))", Classes)' \
  'multiplier <- Parser.term(theory, notation, "INT_OF_NUM (d:num)", Classes)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cancelling.log" 2>&1
echo "### exit $? for 1-the-multiplier-is-not-a-successor" >> "$OUT/cancelling.log"

# 2. The two sums crossed. Each side is still a sum of the right shape, so nothing here is
# ill-typed and nothing is a false ring identity on its own; what breaks is that the semiring is
# asked to rearrange the raw equation into two halves it does not belong to, and `Semiring.prove`
# refuses with two normal forms rather than searching.
echo "################ 2-the-two-sums-crossed" >> "$OUT/cancelling.log"
"$P" "$SOURCE" \
  'leftScaled <- carrier.product(successor, leftSum)
      rightScaled <- carrier.product(successor, rightSum)' \
  'leftScaled <- carrier.product(successor, rightSum)
      rightScaled <- carrier.product(successor, leftSum)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/cancelling.log" 2>&1
echo "### exit $? for 2-the-two-sums-crossed" >> "$OUT/cancelling.log"

cd "$WT" && git status --porcelain >> "$OUT/cancelling.log"
