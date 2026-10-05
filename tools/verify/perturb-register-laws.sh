#!/bin/sh
# Fire the guard that gives the sixteen laws of the reals their rows in the reading register, card
# f327c976.
#
# The defect it is written for is an absence: from 2026-09-27 until 2026-10-05 the register had no
# row for any of the sixteen, because the first population is read off `theory.axioms` and the
# change that proved them took them out of it. Nothing went red, since every assertion of
# `RegisterSpec` was about a population that still had all its rows. So the first perturbation puts
# that state back, the population empty, and the guard must name the sixteen.
#
# The second is narrower and is the shape a refactoring would produce: the population is still
# generated and printed, and `Register.rows`, which the document test and the attestation check
# read, forgets it. The sum in "carry a row for every statement" is what has to notice.
#
# WHAT WAS SEEN, 2026-10-05, on the tree that landed this. Control green at 12 tests, both red,
# restore verified by the tool each time.
#
#   1. "a law of the reals not in the register: ADD_SYM, ADD_ASSOC, ..., COMPLETENESS", all sixteen
#      named, and the document test red beside it because the generated section changed.
#   2. "214 was not equal to 230" in the row sum, and the attestation test red on the same count:
#      sixteen rows the document prints and the checks do not read.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Register.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.RegisterSpec'

echo "################ 0-control" >> "$OUT/register-laws.log"
./tools/sbt -batch "$SPEC" >> "$OUT/register-laws.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/register-laws.log"

# 1. The population empty, which is the register as it stood from 2026-09-27 to 2026-10-05.
echo "################ 1-no-laws" >> "$OUT/register-laws.log"
"$P" "$SOURCE" \
  '    Real.Laws.map { case (name, _) =>' \
  '    Real.Laws.take(0).map { case (name, _) =>' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/register-laws.log" 2>&1
echo "### exit $? for 1-no-laws" >> "$OUT/register-laws.log"

# 2. The laws generated and printed, and left out of the rows every other check reads.
echo "################ 2-rows-forget-the-laws" >> "$OUT/register-laws.log"
"$P" "$SOURCE" \
  '    axiomRows(chain) ++ lawRows(chain) ++ definitionRows(chain) ++ notationRows(chain)' \
  '    axiomRows(chain) ++ definitionRows(chain) ++ notationRows(chain)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/register-laws.log" 2>&1
echo "### exit $? for 2-rows-forget-the-laws" >> "$OUT/register-laws.log"
