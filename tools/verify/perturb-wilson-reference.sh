#!/bin/sh
# Fire the comparison of Wilson's theorem with a reference computed outside the kernel, card 943e4091.
#
# `WilsonAtSmallPrimesSpec` detaches `NUM_WILSON` at 2, 3, 5 and 7 and compares the kernel's value of
# `SUC (NUM_FACT (PRE p))` with `(p - 1)! + 1` computed by BigInt. The perturbation moves the
# reference to `(p - 1)! + 2`, and both tests that read it must go red: the detachment (the kernel's
# value no longer matches) and the refutation at the composites (the refutation is built at the
# reference's value). The third test does not read the reference and stays green.
#
# WHAT WAS SEEN, 2026-09-27, verifying 943e4091: the same substitution compiled by scala-cli against
# the classes of 7a15f023 (main sources identical to 2cb685b7): 2 tests failed, 1 succeeded, the
# first failure reading `at 2: (SUC (SUC ZERO)) was not equal to (SUC (SUC (SUC ZERO)))`.
# Unperturbed, 3 of 3 green.
#
# This script has not yet been run through sbt. Record its first run here when it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/WilsonAtSmallPrimesSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.WilsonAtSmallPrimesSpec'

echo "################ 0-control" >> "$OUT/wilson-reference.log"
./tools/sbt -batch "$SPEC" >> "$OUT/wilson-reference.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/wilson-reference.log"

echo "################ 1-reference-plus-two" >> "$OUT/wilson-reference.log"
"$P" "$SOURCE" \
  'private def reference(p: Int): BigInt = factorial(p - 1) + 1' \
  'private def reference(p: Int): BigInt = factorial(p - 1) + 2' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/wilson-reference.log" 2>&1
echo "### exit $? for 1-reference-plus-two" >> "$OUT/wilson-reference.log"

cd "$WT" && git status --porcelain >> "$OUT/wilson-reference.log"
