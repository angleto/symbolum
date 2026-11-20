#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_EXISTS_BELOW_NUMERAL` and
# `NUM_PROV_NOT_EXISTS_BELOW_NUMERAL`, that what each stands on is load-bearing rather than beside it.
#
# 1. The witness half puts `numeral k` for `v_x` inside `v_x < numeral n`, which is a universal
#    over `v_i`, so the substitution has to decide whether `i` is `x`. With `~(i = x)` withheld from
#    the comparisons `Language` is handed, that decision cannot be made and the chain should refuse
#    to build at this fact.
# 2. The refutation half needs `~(v_x < n /\ p)`, which the encoding of `/\` makes `~~(v_x < n ==>
#    ~p)`, and not `v_x < n ==> ~p`, which is what the universal half hands over. With the double
#    negation under the quantifier dropped, the generalisation is handed `(!v_x. B) ==> B` where it
#    was asked for `~~B`, and the chain should refuse to build at this fact.
# 3. `OpenSteps.wf` gained one case, a universal, for codes around `p` that are not concrete. The
#    refutation half asks it of `!v_x. v_x < numeral n ==> ~p`. With the case removed, the code
#    falls through to `Language.wellFormedIn`, which cannot walk `p`, and the chain should refuse.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-20, on the tree that became the commit carrying this file: the control
# green at 24 of 24, and each perturbation aborting `DeductionSpec` before any test ran, at
# `Chain.standard`, with the tree restored after each.
# 1. "the standard chain does not build: expected a numeral of num, found i". The refusal comes
#    from the index comparison `Language` falls back to when nobody told it the two indices
#    differ, and it does not name the fact: the prediction said "by name" and was wrong there.
# 2. "expected a proof of the implication's antecedent, found (NUM_PROV ...)", at modus ponens
#    with the undoubled body as the antecedent on offer.
# 3. "expected a code of the object language with a literal tag, found (((NUM_LESS i) ((NUM_CODE
#    ZERO) x)) (NUM_NUMERAL n))", `Language.wellFormedIn` meeting the bound it cannot walk.
# None of the three names the fact it stopped at; what attributes each to its own perturbation
# is that each message differs from the other two, and the control, with none of them, is green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DEDUCTION=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Deduction.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/exists-below.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-witness-without-the-indices-apart" >> "$LOG"
"$P" "$DEDUCTION" \
  '      new OpenSteps(Vector(assumed(indicesApart)), Map(Term.variable("p", numbers) -> assumed(isFormula)))
        .existsBelow(indicesApart, isFormula)' \
  '      new OpenSteps(Vector.empty, Map(Term.variable("p", numbers) -> assumed(isFormula)))
        .existsBelow(indicesApart, isFormula)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-witness-without-the-indices-apart" >> "$LOG"

echo "################ 2-refutation-without-the-double-negation" >> "$LOG"
"$P" "$DEDUCTION" '          .flatMap(rules.mp(_, toDoubled))) // (!v_x. B) ==> !v_x. ~~B' \
  '          .flatMap(rules.mp(_, specialised))) // (!v_x. B) ==> !v_x. ~~B' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-refutation-without-the-double-negation" >> "$LOG"

echo "################ 3-wf-without-the-universal-case" >> "$LOG"
"$P" "$DEDUCTION" \
  '          case App(App(head, t8), App(App(join, bound), body)) if head == coding && t8 == tag(8) && join == pairing =>
            force(rules.specAll(universalIsFormula, List(bound, body)).flatMap(rules.mp(_, wf(body))))
' '' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-wf-without-the-universal-case" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
