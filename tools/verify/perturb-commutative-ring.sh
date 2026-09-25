#!/bin/sh
# Fire CommutativeRingSpec at the defect its cancellation test was written for, card fa8737ad.
#
# The order counted a negation's node in the size one level down, so `-(x * y)` sorted after every
# product of its shape instead of beside `x * y`, and the cancellation never met its pair. It was
# found as the refusal of the rationals' first obligation on 2026-09-25. The perturbation puts that
# counting back, and FractionSpec, where the defect was seen, must go red; the control before it
# must be green. CommutativeRingSpec runs beside it and is expected to STAY green: its cancellation
# case was written for this defect and, fired here on 2026-09-25, did not see it, because three
# monomials of one shape never reach the level of the recursion where the node was counted.
#
# WHAT WAS SEEN, 2026-09-25, on the tree that landed this: control green at 12 tests; perturbed,
# FractionSpec aborted at construction with the ring refusing the sum's obligation, `m` and `-m`
# standing four summands apart in the normal form, and CommutativeRingSpec green at 5, as
# predicted above. Restore verified by the tool.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/CommutativeRing.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CommutativeRingSpec garden.xeno.symbolum.theories.FractionSpec'

echo "################ 0-control" >> "$OUT/commutative-ring.log"
./tools/sbt -batch "$SPEC" >> "$OUT/commutative-ring.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/commutative-ring.log"

echo "################ 1-the-negation-counted-in-the-size" >> "$OUT/commutative-ring.log"
"$P" "$SOURCE" \
  'case App(Const(name, _), argument) if negation.contains(name) => size(argument)' \
  'case App(Const(name, _), argument) if negation.contains(name) => 1 + size(argument)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/commutative-ring.log" 2>&1
echo "### exit $? for 1-the-negation-counted-in-the-size" >> "$OUT/commutative-ring.log"
