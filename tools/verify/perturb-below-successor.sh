#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_LESS_SUC_CASES`, that the change it makes below
# `Deduction` is needed at both doors: `Language` taking the comparisons it cannot make between
# open indices as facts the caller supplies, once in `substituteIn` and once in the decision shared
# by `substitutableIn`, `freeInTerm` and `freeInFormula`.
#
# Each perturbation removes the use of the supplied facts at one door and leaves the other, so a
# comparison between `x` and `i`, or between either and the hole, is refused again. If one door did
# not need them, its perturbed run would read like the control and that half of the change would
# not belong. What each perturbed run should show is the chain refusing to build at this fact.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-18 over ec0af3d1 plus the increment: control, DeductionSpec 21 of 21;
# the substitution door shut, the suite aborted with "the standard chain does not build: expected
# a numeral of num, found (SUC (SUC ((NUM_ADD i) x)))"; the decision door shut, it aborted with
# "expected an answer made of T and F alone, found ((\/ (x = i)) F)"; the file restored from the
# captured bytes after each.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Language.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/below-successor.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-substitution-ignores-the-supply" >> "$LOG"
"$P" "$FILE" '              else supplied.find(_.conclusion == equalsFalse(guard)) match {
                case Some(known) => Right(known)
                case None =>' '              else Option.empty[Kernel.Thm] match {
                case Some(known) => Right(known)
                case None =>' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-substitution-ignores-the-supply" >> "$LOG"

echo "################ 2-decision-ignores-the-supply" >> "$LOG"
"$P" "$FILE" '                else if (supplied.exists(_.conclusion == equalsFalse(guard)))
                  Right(found ++ supplied.filter(_.conclusion == equalsFalse(guard)))
                else if (Term.freeVariables' '                else if (Term.freeVariables' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-decision-ignores-the-supply" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
