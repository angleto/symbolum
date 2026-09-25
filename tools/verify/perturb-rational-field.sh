#!/bin/sh
# Fire the rationals' inverse at the two places its derivation is supposed to depend on, card 5ef905fc.
#
# 1. The definition's zero branch is `RAT_ZERO`, and `RAT_INV_ZERO` is derived from it through the
#    conditional rather than asserted. Pointing the branch at `RAT_ONE` must make the construction
#    refuse that fact; a construction that still produced it would be producing it from somewhere
#    other than the definition.
# 2. A negative numerator `-(k + 1)` is inverted by the class of `(-(d + 1), k)`, and the sign is
#    what makes the product `(d + 1) * (k + 1)` rather than its negation. Dropping it in the
#    negative case must make the existence refuse; if it did not, the sign split would be carrying
#    nothing and the positive case alone would be deciding every rational.
#
# FractionSpec is the spec: every fact is derived inside `Fraction.construct`, so a refusal there
# aborts the suite at construction, which is the red this expects. The control before must be green.
#
# WHAT WAS SEEN, 2026-09-25: control green at 13 tests. Perturbed, 1 aborted construction with
# `RAT_INV RAT_ZERO = RAT_ONE` found where the published statement was expected, and 2 aborted it
# with the ring refusing the product's numerator, which came out as the negation of the one the
# relation needs. Restore verified by the tool after each.
#
# The first run of 1 stayed GREEN, and the reason is this harness rather than the derivation: the
# target read `COND (x = RAT_ZERO) RAT_ZERO (select`, which `Fraction`'s own docstring also holds,
# and the tool replaces the first occurrence without refusing a text that occurs twice, so the
# perturbation landed in a comment. The target now starts at the literal's `x:rat.`, which occurs
# once. A green perturbation is worth a count of the target before it is believed.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Fraction.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.FractionSpec'
LOG="$OUT/rational-field.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-zero-branch-is-one" >> "$LOG"
"$P" "$SOURCE" \
  'x:rat. COND (x = RAT_ZERO) RAT_ZERO (select' \
  'x:rat. COND (x = RAT_ZERO) RAT_ONE (select' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-zero-branch-is-one" >> "$LOG"

echo "################ 2-the-negative-witness-unsigned" >> "$LOG"
"$P" "$SOURCE" \
  'inverseNumerator <- signed(denominator)' \
  'inverseNumerator <- Right(denominator)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-negative-witness-unsigned" >> "$LOG"
