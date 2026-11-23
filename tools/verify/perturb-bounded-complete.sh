#!/bin/sh
# Measure, for card 4102f131's increment `NUM_PROV_BOUNDED`, that the two facts the universal's
# case stands on beside the four of `Deduction` are load-bearing rather than beside it.
#
# 1. The rank. An instance is handed to the hypothesis with the body's rank below the universal's
#    rather than its own, which `NUM_RANK_SUBST_NUMERAL` equates. The hypothesis is read at the
#    instance's rank, so the chain should refuse to build at the universal's case.
# 2. The bound. A closed universal of the class has a numeral for its bound because a variable
#    bound would be free in it. With that refutation replaced by the numeral case assumed, the
#    variable case is no longer closed off, and the chain should refuse to build or the theorem
#    should come out owing the assumption; which of the two is what this run says.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-22, on the tree that became the commit carrying this file: the control
# green at 17 of 17, the tree restored afterwards, and both perturbations as predicted.
# 1. All 17 red, every one at `Chain.standard`: "expected a proof of the implication's
#    antecedent, found ((NUM_LT (NUM_RANK r)) n)", the hypothesis asked at the instance's rank
#    and offered the body's.
# 2. All 17 red, every one at `Chain.standard`, so the first of the two outcomes: "c occurs free
#    in 1 of the hypotheses: (? (\x:num. (c = (NUM_NUMERAL x))))". The assumption let through
#    stays a hypothesis, and generalising over the bound refuses on it before a theorem owing it
#    could come out.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/bounded-complete.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-body-rank-for-the-instance" >> "$LOG"
"$P" "$TRUTH" '                      val rankBelow = moved(t => lessThan(t, n), force(Conv.sym(rankIs)), rBelow)' \
  '                      val rankBelow = rBelow' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-body-rank-for-the-instance" >> "$LOG"

echo "################ 2-a-variable-bound-let-through" >> "$LOG"
"$P" "$TRUTH" '                    absurd(numeralHad, notVariable), assumed(numeralHad))) // ?count. c = NUM_NUMERAL count' \
  '                    assumed(numeralHad), assumed(numeralHad))) // ?count. c = NUM_NUMERAL count' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-a-variable-bound-let-through" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
