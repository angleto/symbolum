#!/bin/sh
# Re-fire the guard of card 354256d9 at the defect it was written for: Model.Reals leaving inv 0
# undefined, and the alternative it rejects, inv 0 as IEEE infinity.
#
# The guard is "say at zero what the chain proves there" in EvaluateSpec. The string below is
# literal and was unique when the card landed. perturb.sh REFUSES a perturbation that did not apply
# rather than running against unperturbed code, so a refusal means the source moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

MODEL=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Model.scala
SPEC='tactics/testOnly garden.xeno.symbolum.tactics.EvaluateSpec'
FIXED='unary(argument => Some(if (argument == 0.0) 0.0 else 1.0 / argument))'

run() { n="$1"; shift
  echo "################ $n" >> "$OUT/inverse-at-zero.log"
  "$P" "$@" >> "$OUT/inverse-at-zero.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/inverse-at-zero.log"
}

# 0. THE CONTROL: the same command green without a perturbation.
echo "################ 0-control" >> "$OUT/inverse-at-zero.log"
./tools/sbt -batch "$SPEC" >> "$OUT/inverse-at-zero.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/inverse-at-zero.log"

# 1. The defect: inv 0 undefined, which is what the model said from its first line to 2026-11-10.
# Expect red on: "say at zero what the chain proves there" (inv x = 0 at 0 comes back None).
run "1-undefined" "$MODEL" \
  "$FIXED" \
  'unary(argument => if (argument == 0.0) None else Some(1.0 / argument))' \
  -- ./tools/sbt -batch "$SPEC"

# 2. The rejected alternative: no guard on zero, so 1.0 / 0.0 is Infinity.
# Expect red on the same test, and NOT where one would guess: `inv x = 0` at 0 comes back
# Some(true), because Evaluate.indistinguishable scales its tolerance by the larger magnitude and
# an infinite scale calls Infinity equal to 0. The red is `x * inv x * x = x`, which is NaN there.
# Observed so on 2026-11-10.
run "2-infinity" "$MODEL" \
  "$FIXED" \
  'unary(argument => Some(1.0 / argument))' \
  -- ./tools/sbt -batch "$SPEC"

echo "### both fired" >> "$OUT/inverse-at-zero.log"
git status --porcelain >> "$OUT/inverse-at-zero.log"
