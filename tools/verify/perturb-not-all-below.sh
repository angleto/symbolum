#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_NOT_ALL_BELOW_NUMERAL`, that what it stands on
# is load-bearing rather than beside it.
#
# 1. Specialising at `numeral k` puts it for `v_x` inside `v_x < numeral n`, a universal over
#    `v_i`, so the substitution has to decide whether `i` is `x`. With `~(i = x)` withheld from
#    the comparisons `Language` is handed, the chain should refuse to build.
# 2. The instance of the universal is `numeral k < numeral n ==> p[numeral k/x]`, and it is the
#    order, detached under the universal, that leaves `p[numeral k/x]` to contrapose. With the
#    detachment dropped, contraposition yields `~(order ==> p[k/x]) ==> ~(!v_x. B)`, and modus
#    ponens with the refuted instance should refuse.
# 3. The substitution into the order is computed and not left standing. With that computation
#    dropped from the rewrite, the antecedent stays `NUM_SUBST_FORM x (numeral k) (order)` and is
#    not the code `NUM_PROV_LESS_NUMERAL` proves, so the detachment should refuse.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-21, on the tree that became the commit carrying this file: the control
# green at 25 of 25, and each perturbation aborting `DeductionSpec` before any test ran, at
# `Chain.standard`, with the tree restored after each, as predicted.
# 1. "expected a numeral of num, found i", the index comparison `Language` falls back to, which is
#    the message the existential half's harness saw under the same perturbation.
# 2. "expected a proof of the implication's antecedent, found (NUM_PROV (NUM_CODE 6
#    (NUM_SUBST_FORM x (NUM_NUMERAL k) p)))": the refuted instance offered where the denial of
#    the whole instance, order included, was wanted.
# 3. "expected a proof of the implication's antecedent, found (NUM_PROV (NUM_CODE 7 (NUM_PAIR
#    (NUM_CODE 8 (NUM_PAIR x ...": the order `NUM_PROV_LESS_NUMERAL` proves, weakened under the
#    universal, offered where the substitution into the order was wanted, left standing.
# None of the three names the fact; each message differs from the other two, and the control,
# with none of them, is green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DEDUCTION=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Deduction.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/not-all-below.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-without-the-indices-apart" >> "$LOG"
"$P" "$DEDUCTION" \
  '      new OpenSteps(Vector(assumed(indicesApart)), Map(Term.variable("p", numbers) -> assumed(isFormula)))
        .notAllBelow(indicesApart, isFormula)' \
  '      new OpenSteps(Vector.empty, Map(Term.variable("p", numbers) -> assumed(isFormula)))
        .notAllBelow(indicesApart, isFormula)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-without-the-indices-apart" >> "$LOG"

echo "################ 2-without-the-order-detached" >> "$LOG"
"$P" "$DEDUCTION" '        val toInstance = collapsed(specialised, ordered) // (!v_x. B) ==> p[numeral k/x]' \
  '        val toInstance = specialised // (!v_x. B) ==> p[numeral k/x]' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-without-the-order-detached" >> "$LOG"

echo "################ 3-without-the-order-computed" >> "$LOG"
"$P" "$DEDUCTION" \
  '          force(language.fact(Language.FormulaSubstituteNegation)),
          computed(x, witness, order)) // (!v_x. B) ==> (numeral k < numeral n ==> p[numeral k/x])' \
  '          force(language.fact(Language.FormulaSubstituteNegation))) // (!v_x. B) ==> (numeral k < numeral n ==> p[numeral k/x])' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-without-the-order-computed" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
