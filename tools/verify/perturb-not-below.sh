#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_NOT_LESS_NUMERAL`, that the one change it makes
# below `Deduction` is needed: `Language.decideSyntax` leaving an index pair with a free variable
# undecided rather than refusing it.
#
# The perturbation puts back the line as it was before the increment, so a pair with a free
# variable goes to `Successor.distinct` again, which refuses it. If the derivation did not need the
# change, the control and the perturbed run would read the same, and the change would not belong.
# What the perturbed run should show is the chain refusing to build at this fact.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-17 over cd416282 plus the increment: control, DeductionSpec 20 of 20;
# perturbed, the suite aborted with "the standard chain does not build: expected a numeral of num,
# found n", and the file restored from the captured bytes.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Language.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/not-below.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-open-pairs-refused" >> "$LOG"
"$P" "$FILE" 'else if (Term.freeVariables(one).nonEmpty || Term.freeVariables(other).nonEmpty)
                  Right(found)
                else' 'else' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-open-pairs-refused" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
