#!/bin/sh
# Fire SemiringDecidesOnlyFreeAtomsSpec, card 22eb8f25: a semiring refusal standing Decided against a theorem.
#
# `CommutativeRing.prove` reads a `NotEqualTo` again and keeps it `Decided` only when every atom of
# the two normal forms is a free variable. Without that reading the semiring of `num` refuses
# `NUM_SUB n n = 0` and `n + SUC m = SUC (n + m)`, both theorems of the library, as decided.
#
# WHAT WAS SEEN, 2026-09-28, through sbt: clean green at 2 tests; with the reading removed red at 1
# of 2, the one test naming both statements, each `NotEqualTo, Decided`, and the control green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/CommutativeRing.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SemiringDecidesOnlyFreeAtomsSpec'

echo "################ 0-control" >> "$OUT/semiring-reading.log"
./tools/sbt -batch "$SPEC" >> "$OUT/semiring-reading.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/semiring-reading.log"

# 1. The refusal left as `Rewrite` raised it: red, naming both statements.
echo "################ 1-no-reading" >> "$OUT/semiring-reading.log"
"$P" "$SOURCE" "Rewrite.proveEquation(logic, normalisation, goal).left.map(asRead)" \
  "Rewrite.proveEquation(logic, normalisation, goal)" -- ./tools/sbt -batch "$SPEC" >> "$OUT/semiring-reading.log" 2>&1
echo "### exit $? for 1-no-reading" >> "$OUT/semiring-reading.log"
