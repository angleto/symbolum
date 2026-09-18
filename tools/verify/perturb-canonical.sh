#!/bin/sh
# Re-fire the two guards of card 325ec342 at the defects they were written for.
#
# Both guards are properties in CanonicalFormSpec and both were observed red before the commit;
# this is what lets a later verifier confirm that without taking the delivery's word for it.
#
# The strings are literal and were unique at 24a905f. perturb.sh REFUSES a perturbation that did
# not apply rather than running against unperturbed code, so a refusal means the source moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

CANON=modules/core/src/main/scala/garden/xeno/symbolum/Canonical.scala
SPEC='core/testOnly garden.xeno.symbolum.CanonicalFormSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$OUT/canonical.log"
  "$P" "$@" >> "$OUT/canonical.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/canonical.log"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it, and perturb.sh says of itself that it does not decide whether a red is the RIGHT red.
echo "################ 0-control" >> "$OUT/canonical.log"
./tools/sbt -batch "$SPEC" >> "$OUT/canonical.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/canonical.log"

# 1. The sum back in arrival order: the original defect. Double addition is commutative and not
# associative, so three contributions on one base cancel to zero one way and to an epsilon the
# other, and isZero does not discard an epsilon.
# Expect red on: "a product whose coefficients cancel inexactly is the same both ways round"
run "1-arrival-order" "$CANON" \
  'parts.sortBy(coefficientOrder).foldLeft(Zero)(numAdd)' \
  'parts.foldLeft(Zero)(numAdd)' \
  -- ./tools/sbt -batch "$SPEC"

# 2. Order by value alone: sortBy is stable, so a tie between two DIFFERENT fractions that share a
# double (2^54/2^55 normalises to (0.5,1.0); a half is (1.0,2.0)) leaves arrival order standing.
# Expect red on: "a coefficient tie across the exactness limit is summed the same way round"
run "2-value-only-order" "$CANON" \
  'parts.sortBy(coefficientOrder)' \
  'parts.sortBy(n => Rational.value(n.fraction))' \
  -- ./tools/sbt -batch "$SPEC"

echo "### both fired" >> "$OUT/canonical.log"
git status --porcelain >> "$OUT/canonical.log"
