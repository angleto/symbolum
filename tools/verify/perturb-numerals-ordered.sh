#!/bin/sh
# Fire the guards of card 4102f131's increment that makes PA prove a true strict order between
# numerals: `NUM_PROV_EXISTS_INTRO` and `NUM_PROV_LESS_NUMERAL` in `Deduction`.
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own.
#
# WHAT WAS SEEN, 2026-11-10, on the tree that landed this. Control green (DeductionSpec 14);
# every perturbation red, restores verified, tree clean after.
#
#   1. The witness one too far, `numeral (SUC d)`: the suite aborts with "the standard chain does
#      not build: modus ponens on an equation", the computed instance `numeral m + S (numeral
#      (SUC d)) = numeral n` no longer being the numeral sum PA was shown to prove.
#   2. Existential introduction without the double negation: the suite aborts with "expected a
#      proof of the implication's antecedent, found NUM_PROV (NUM_SUBST_FORM i t p)", tollens
#      wanting `~~p[t/i]` there.
#   3. The order's binders published as `!m n i.` with the proof generalised to match: the
#      statement test stays green, because the fact is consistent with its text, and the test of
#      the strict order goes red alone, 13 of 14, since its instance is read at `i, m, n`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Deduction.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DeductionSpec'
LOG="$OUT/numerals-ordered.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

run() {
  name=$1; from=$2; to=$3
  echo "################ $name" >> "$LOG"
  "$P" "$FILE" "$from" "$to" -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-witness-too-far 'val witness = numeral(d)' 'val witness = numeral(suc(d))'
run 2-no-double-negation 'specialised, doubled)' 'specialised, assumed(holds))'

echo "################ 3-binders-reordered" >> "$LOG"
"$P" "$FILE" '"!i:num m:num n:num. m < n ==> NUM_PROV (NUM_LESS i' \
  '"!m:num n:num i:num. m < n ==> NUM_PROV (NUM_LESS i' -- \
  "$P" "$FILE" 'force(rules.disch(below, reached).flatMap(rules.genAll(_, List(i, m, n))))' \
  'force(rules.disch(below, reached).flatMap(rules.genAll(_, List(m, n, i))))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-binders-reordered" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
