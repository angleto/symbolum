#!/bin/sh
# Fire the claim that every printed binder is named from its type's list, card 14b83bac.
#
# `Show.binderName` offers a function f, g, h. The perturbation hands a function the values' list
# again, which is the printer as it was before 2026-09-26, and `BinderNamesByTypeSpec` must go red
# in three of its four tests: the census over the printed library (a function named x), the mean
# value theorem's opening, and the unit test on `Show.binderName`. The fourth, that the page is read
# whole, is the census's completeness control and does not depend on the names, so it stays green.
#
# WHAT WAS SEEN, 2026-09-27, verifying 14b83bac: the same substitution compiled by scala-cli against
# the classes of 7a15f023 (main sources identical to 2cb685b7), the patched Show.scala shadowing the
# built one: 3 tests failed, 1 succeeded, and the census named FUNCTION_EXTENSIONALITY, NOT_FORALL
# and the rest. Unperturbed, 4 of 4 green.
#
# This script has not yet been run through sbt. Record its first run here when it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Show.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.BinderNamesByTypeSpec'

echo "################ 0-control" >> "$OUT/binder-names.log"
./tools/sbt -batch "$SPEC" >> "$OUT/binder-names.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/binder-names.log"

echo "################ 1-functions-named-as-values" >> "$OUT/binder-names.log"
"$P" "$SOURCE" \
  'case TyApp("fun", List(_, _)) => Functions' \
  'case TyApp("fun", List(_, _)) => Values' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/binder-names.log" 2>&1
echo "### exit $? for 1-functions-named-as-values" >> "$OUT/binder-names.log"

cd "$WT" && git status --porcelain >> "$OUT/binder-names.log"
