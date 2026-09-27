#!/bin/sh
# Fire the reading of TAYLOR at the cube's Lagrange point, card 4942ffdb.
#
# `TaylorAtACubeSpec` detaches `TAYLOR` at the cube and its two derivatives, order one, on [0, 1],
# and settles the remainder equation to `1 = c * 3` with `Field`. The perturbation asks for the point
# of a different remainder, `1 = c * 2`, and the test must go red because `Field` refuses the
# identity; the detachment test does not read the point and stays green.
#
# WHAT WAS SEEN, 2026-09-27, verifying 4942ffdb: the same substitution compiled by scala-cli against
# the classes of 7a15f023 (main sources identical to 2cb685b7): 1 test failed, 1 succeeded.
# Unperturbed, 2 of 2 green.
#
# This script has not yet been run through sbt. Record its first run here when it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/TaylorAtACubeSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TaylorAtACubeSpec'

echo "################ 0-control" >> "$OUT/taylor-point.log"
./tools/sbt -batch "$SPEC" >> "$OUT/taylor-point.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/taylor-point.log"

echo "################ 1-point-one-half" >> "$OUT/taylor-point.log"
"$P" "$SOURCE" \
  'real("(c:real) * (1 + 1 + 1)")' \
  'real("(c:real) * (1 + 1)")' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/taylor-point.log" 2>&1
echo "### exit $? for 1-point-one-half" >> "$OUT/taylor-point.log"

cd "$WT" && git status --porcelain >> "$OUT/taylor-point.log"
