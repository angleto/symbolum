#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_SIGMA`, that the step of the induction rests on
# the existential binding its index and on the witness the truth gave, rather than beside them.
#
# 1. The binder. The instance is closed because a variable free in it is free in the body and is
#    not the index, and a variable free in the body and not the index is free in the existential.
#    With the existential's clause dropped, the body's freeness is offered where the whole's is
#    asked, and the chain should refuse to build at the step's closedness.
# 2. The witness. The existential is introduced at the numeral of the successor of the value the
#    truth gave rather than at that value, so the instance PA is asked to have proved is not the one
#    the hypothesis proved, and the chain should refuse to build at the introduction.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-24, on the tree that became the commit carrying this file: the control
# green at 18 of 18, the tree restored after each perturbation, and both as predicted.
# 1. All 18 red, every one at `Chain.standard`: "modus ponens on an equation: ((NUM_FREE_FORM f)
#    ((NUM_EXISTS j) q)) is not ((NUM_FREE_FORM f) q)", the body's freeness offered where the
#    existential's was asked.
# 2. All 18 red, every one at `Chain.standard`: "expected a proof of the implication's antecedent,
#    found (NUM_TERM (NUM_NUMERAL m))", the introduction asked for the successor's numeral and given
#    the witness's.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/sigma-complete.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-body-for-the-existential" >> "$LOG"
"$P" "$TRUTH" '              val atWhole = moved(t => freeForm(f, t), back, atShape)' \
  '              val atWhole = moved(t => freeForm(f, t), back, force(rules.conjElim1(survived)))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-body-for-the-existential" >> "$LOG"

echo "################ 2-another-witness" >> "$LOG"
"$P" "$TRUTH" 'val introducedShape = apply(deductionFact(Deduction.ExistentialIntroduction), List(j, numeral(m), q),' \
  'val introducedShape = apply(deductionFact(Deduction.ExistentialIntroduction), List(j, numeral(applied(successorConstant, List(m))), q),' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-another-witness" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
