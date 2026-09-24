#!/bin/sh
# Fire the both-directions guards of card 601788d5 at the defect each was written for.
#
# The card widened db67b658's census from a count followed by its plural noun to a count, a
# modifier, then the plural, and found three sites that reach one: `RestsOn`'s "1 named facts",
# `Cnf`'s "within the 1 declared variables" and `Remedy`'s "over 1 linear constraints". Beside the
# last sat a fourth no census of a noun selects, `these 1 cannot`, where the demonstrative is what
# agrees with the count. Each perturbation below puts ONE site back and leaves the others repaired.
#
# Each guard asserts a singular that is not a substring of its defect: the text after the noun is
# part of every assertion, which is the trap db67b658 met twice.
#
# The strings are literal and were unique when this was written. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/count-modifier-plural.log"
CNF=modules/sat/src/main/scala/garden/xeno/symbolum/sat/Cnf.scala
RESTS=modules/theories/src/main/scala/garden/xeno/symbolum/theories/RestsOn.scala
REMEDY=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Remedy.scala
SAT='sat/testOnly garden.xeno.symbolum.sat.SolverSpec'
THEORIES='theories/testOnly garden.xeno.symbolum.theories.RestsOnSpec'
TACTICS='tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SAT" "$THEORIES" "$TACTICS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Expect red on: SolverSpec, "take the singular when the problem declares one variable"
run "1-declared-variables" "$CNF" \
  'Plural.count(variables, "declared variable", "declared variables")' \
  's"$variables declared variables"' \
  -- ./tools/sbt -batch "$SAT"

# 2. Expect red on: RestsOnSpec, "take the singular at one named fact"
run "2-named-facts" "$RESTS" \
  '${Prose.count(facts.size, "named fact")}' \
  '${facts.size} named facts' \
  -- ./tools/sbt -batch "$THEORIES"

# 3. Expect red on: RemedySpec, "agree with their count at one and elsewhere"
run "3-linear-constraints" "$REMEDY" \
  '${Prose.count(constraints, "linear constraint")}' \
  '$constraints linear constraints' \
  -- ./tools/sbt -batch "$TACTICS"

# 4. Expect red on: RemedySpec, "agree with their count at one and elsewhere"
run "4-these-premises" "$REMEDY" \
  'if (premises == 1) "the one premise here cannot hold, so every conclusion follows from it"' \
  'if (false) ""' \
  -- ./tools/sbt -batch "$TACTICS"

echo "### all four fired" >> "$LOG"
git status --porcelain >> "$LOG"
