#!/bin/sh
# Re-fire the guards of card 3c9417ce at the defects they were written for: Model.Numbers giving the
# numerals of num no value, a model reading the two digits the wrong way round, and the clause that
# InterpretMore printed as "the model says nothing about none of 100 points could be evaluated".
#
# The strings below are literal and were unique when the card landed. perturb.sh REFUSES a
# perturbation that did not apply rather than running against unperturbed code, so a refusal means
# the source moved. An exit of 75 from the build wrapper means the queue gave no slot and nothing
# ran: read it as "not run", never as a result.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/num-numerals.log"
MODEL=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Model.scala
REMEDY=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Remedy.scala
SPECS='tactics/testOnly garden.xeno.symbolum.tactics.RefutationSpec garden.xeno.symbolum.tactics.RemedySpec garden.xeno.symbolum.tactics.ElaborateRoutesSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL: the same command green without a perturbation.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The defect: NUM_ONE has no value, which is what the model said from 2026-09-12 to 2026-11-12.
# Expect red on "be asked, because the numeral has a value" (n + 1 = n is NeverAsked) and on the
# document test in ElaborateRoutesSpec (no `false:` line).
run "1-no-one" "$MODEL" \
  'Peano.NumeralOne -> Whole(1),' \
  'Peano.NumeralOne -> onWhole(_ => None),' \
  -- ./tools/sbt -batch "$SPECS"

# 2. The digits swapped: every numeral still has a value, so the test above stays green where the
# claim is false at small n either way, and the theorems go red. Expect red on "never refute a
# theorem" (n * 2 = n + n is refuted).
run "2-digits-swapped" "$MODEL" \
  'Peano.NumeralBit0 -> onWhole(n => Some(Whole(n + n))),' \
  'Peano.NumeralBit0 -> onWhole(n => Some(Whole(n + n + 1))),' \
  -- ./tools/sbt -batch "$SPECS"

# 3. The clause back. Expect red on "hand it something the sentence can be about" in RemedySpec.
run "3-clause" "$REMEDY" \
  'InterpretMore(s"what the claim mentions at $which ${Prose.count(offered, "point")} offered")' \
  'InterpretMore(s"none of ${Prose.count(offered, "point")} could be evaluated")' \
  -- ./tools/sbt -batch "$SPECS"

echo "### all three attempted; read each exit above, 75 is not a result" >> "$LOG"
git status --porcelain >> "$LOG"
