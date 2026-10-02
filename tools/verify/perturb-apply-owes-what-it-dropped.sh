#!/bin/sh
# Fire card 39429606's two repairs, `Apply` owing only what it dropped and `Chaining.closedByLeaf`, at the specs that pin them.
#
# The card: `Ask` answered `Unsettled` to `COS_INJECTIVE` and `PI_HALF_LEAST_ZERO` asked verbatim,
# and to `PI_HALF_LEAST_ZERO` curried. Two causes, one under the other. `Apply.to` counted every
# antecedent of the instance as an obligation, so the scan refused a lemma that IS the goal; and
# the search under the goal's hypotheses, which was the only other route, ranked the lemma behind
# five candidates owing the goal restated and ran out of its ten expansions first.
#
# What has to be seen is that each perturbation reddens its own witnesses and not the other's:
#   1. `Apply` owing every antecedent again: the `LibrarySpec` test, the verbatim `ProveSpec` test,
#      `ShowcaseSpec`'s partition (NUM_INDUCTION and NUM_CRT refused again) and `RediscoverySpec`'s
#      price (the fourteen re-derived by LINARITH) go red. The curried one is not asserted either
#      way here, since the leaf pass may still reach the lemma through the facts.
#   2. The leaf pass switched off: the curried `ProveSpec` test goes red and the other four stay
#      green.
# A perturbation that reddened all of them would mean the tests are not telling the two apart.
#
# Run on 2026-10-02 over the branch `ask-equation-hypothesis` off 7.0 `209c4ab4`, through the
# build queue: the control green at 5 of 5; the first perturbation red on exactly its four, each an
# assertion failure, with the curried one green because the leaf pass reaches it through the facts;
# the second red on the curried one alone.
#
# Each spec runs in its own sbt invocation, because a sequence stops at its first failure and
# perturbation 1 is about every one of its witnesses failing.
#
# The control is the run before them, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

APPLY=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Apply.scala
CHAINING=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Chaining.scala
LIBRARY='theories/testOnly garden.xeno.symbolum.theories.LibrarySpec -- -z "applied to itself"'
VERBATIM='tactics/testOnly garden.xeno.symbolum.tactics.ProveSpec -- -z "lemma with premises asked verbatim"'
CURRIED='tactics/testOnly garden.xeno.symbolum.tactics.ProveSpec -- -z "same lemma curried"'
SHOWCASE='tactics/testOnly garden.xeno.symbolum.tactics.ShowcaseSpec -- -z "proportion measured"'
PRICE='tactics/testOnly garden.xeno.symbolum.tactics.RediscoverySpec -- -z "price of citing"'
LOG="$OUT/apply-owes-what-it-dropped.log"

echo "################ 0-control" >> "$LOG"
for spec in "$LIBRARY" "$VERBATIM" "$CURRIED" "$SHOWCASE" "$PRICE"; do
  ./tools/sbt -batch "$spec" >> "$LOG" 2>&1
  echo "### exit $? for 0-control: $spec" >> "$LOG"
done

echo "################ 1-apply-owes-every-antecedent" >> "$LOG"
for spec in "$LIBRARY" "$VERBATIM" "$CURRIED" "$SHOWCASE" "$PRICE"; do
  "$P" "$APPLY" \
    'peel(logic, instance.conclusion, Vector.empty)._1.take(owed),' \
    'peel(logic, instance.conclusion, Vector.empty)._1,' \
    -- ./tools/sbt -batch "$spec" >> "$LOG" 2>&1
  echo "### exit $? for 1-apply-owes-every-antecedent: $spec" >> "$LOG"
done

echo "################ 2-no-leaf-pass" >> "$LOG"
for spec in "$LIBRARY" "$VERBATIM" "$CURRIED" "$SHOWCASE" "$PRICE"; do
  "$P" "$CHAINING" \
    '    if (depth <= 1) None' \
    '    if (depth <= Int.MaxValue) None' \
    -- ./tools/sbt -batch "$spec" >> "$LOG" 2>&1
  echo "### exit $? for 2-no-leaf-pass: $spec" >> "$LOG"
done

cd "$WT" && git status --porcelain >> "$LOG"
