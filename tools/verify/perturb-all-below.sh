#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_ALL_BELOW_NUMERAL`, that the two pieces it adds
# below `Deduction` are what it stands on rather than beside it.
#
# 1. The equality case replaces `numeral n` by `v_x` in the formula `p` itself, which leaves the
#    instance `p[v_x/x]`. `NUM_SUBST_FORM_SELF` is what reads that as `p`. With the rewrite dropped,
#    the step should no longer compose, and the chain should refuse to build at this fact.
# 2. `NUM_FREE_FOR_SELF` and `NUM_FREE_FOR_CLOSED` share one clause table and differ only in how the
#    quantifier case shows its binder absent from the term. Handing the self lemma the closed
#    lemma's absence should fail, because `v_i` is not closed; if it built, the parameter would be
#    decorative.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-19 over 04ca5ab4 plus the increment: control, DeductionSpec 23 of 23; the
# self rewrite dropped, the suite aborted with "the standard chain does not build: expected a proof
# of the implication's antecedent, found (NUM_PROV ...)"; the closed absence handed to the self
# lemma, it aborted with "modus ponens on an equation: (NUM_CLOSED m) is not (m = ((NUM_CODE ZERO)
# n))"; each file restored from the captured bytes, checked against checksums taken before the run.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DEDUCTION=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Deduction.scala
LANGUAGE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Language.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/all-below.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-instance-at-v-x-left-standing" >> "$LOG"
"$P" "$DEDUCTION" 'collapsed(rewritten(logical(replaced), substitutesItself), atBound)' \
  'collapsed(logical(replaced), atBound)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-instance-at-v-x-left-standing" >> "$LOG"

echo "################ 2-self-given-the-closed-absence" >> "$LOG"
"$P" "$LANGUAGE" '          selfBinderAbsent(freeVariable)' '          closedBinderAbsent(closedCases)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-self-given-the-closed-absence" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
