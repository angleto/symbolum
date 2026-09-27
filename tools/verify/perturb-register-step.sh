#!/bin/sh
# Fire the claim that FRACTRAN_REGISTER_STEP says exactly what a step does, card 626ad37f.
#
# `FRACTRAN_STEP_REGISTERS` is an equation between the step and the same fold written on the prime
# registers, and `Fractran.construct` refuses to build unless it is proved. A statement that is
# proved can still be weaker or different from the informal claim, and nothing printed says which
# of its clauses were needed. The two perturbations each weaken the register side the way a reader
# might write it from memory, and the equation must stop being provable.
#
#   1. The test reads the denominator's registers only, `v(q) <= v(n)`, which is the textbook
#      reading for a REDUCED fraction. The program's fractions are not reduced here (docs/adr/0054),
#      and `6/4` applies at `2` while `v_2(4) <= v_2(2)` fails, so the equation is false. Expected
#      RED at the construction.
#   2. The landing drops `0 < m`. At `m = 0` the valuations are what `select` chose, so the
#      registers no longer determine the number. Expected RED at the construction.
#
# WHAT WAS SEEN, 2026-09-27, verifying 626ad37f: the same two substitutions compiled by scala-cli
# against the classes `tools/sbt test` had just built at b727d812 (2868 tests green there), with the
# unperturbed source as the control, which built.
#
#   1. Refused: `expected a proof of the implication's antecedent`, the applicability clause the
#      derivation could not discharge.
#   2. Refused, in a transitivity step whose left side carries `0 < m`.
#
# This script has not yet been run through sbt. Record its first run here when it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Fractran.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.FractranRegistersSpec'

echo "################ 0-control" >> "$OUT/register-step.log"
./tools/sbt -batch "$SPEC" >> "$OUT/register-step.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/register-step.log"

echo "################ 1-denominator-only" >> "$OUT/register-step.log"
"$P" "$SOURCE" \
  '"NUM_LE (NUM_VALUATION p (SND f)) (NUM_VALUATION p n + NUM_VALUATION p (FST f)))) " +' \
  '"NUM_LE (NUM_VALUATION p (SND f)) (NUM_VALUATION p n))) " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/register-step.log" 2>&1
echo "### exit $? for 1-denominator-only" >> "$OUT/register-step.log"

echo "################ 2-no-positive-landing" >> "$OUT/register-step.log"
"$P" "$SOURCE" \
  '"(NUM_LT 0 m /\\ (!p:num. NUM_PRIME p ==> " +' \
  '"((!p:num. NUM_PRIME p ==> " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/register-step.log" 2>&1
echo "### exit $? for 2-no-positive-landing" >> "$OUT/register-step.log"

cd "$WT" && git status --porcelain >> "$OUT/register-step.log"
