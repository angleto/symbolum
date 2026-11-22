#!/bin/sh
# Measure, for card 4102f131's increment `NUM_BOUNDED` and `NUM_BOUNDED_ALL`, that the class's two
# conditions and the two changes to the machinery under it are load-bearing rather than beside it.
#
# 1. The order's witness apart from the quantified index, taken out of the step and of the
#    published clause together, so the chain still builds: `TruthSpec`'s test of the class should
#    go red at the denial of the universal whose order binds its own index.
# 2. A universal whose body is not an order's implication answering `T` instead of `F`: the
#    inversion has no absurd branch left, and the chain should refuse to build at it.
# 3. The admissibility proof's walk through nested codes switched off: the universal's branch
#    recurses two codes down, and defining `NUM_BOUNDED` should be refused.
# 4. `settleGuards` deciding a guard between two codes of one tag by the tags again: the
#    inversion's guard is of that kind, and the chain should refuse to build at it.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-21, on the tree that became the commit carrying this file: the control
# green at 12 of 12, the tree restored after each perturbation, and all four as predicted.
# 1. 11 of 12 green and the class's test red at the own-index denial: "unexpected refusal:
#    NotOfForm(a negation, ...)", the clause's first conjunct now being the bound's disjunction
#    where `~(0 = 0)` stood. The chain builds, so only the test says the condition is there.
# 2. All 12 red at `Chain.standard`: "expected a proof of falsity, found T".
# 3. All 12 red at `Chain.standard`: "expected a component of the shape the guard gives, found
#    (NUM_SND (NUM_PAYLOAD (NUM_SND (NUM_PAYLOAD n))))", the order's bound two codes down.
# 4. All 12 red at `Chain.standard`: "expected two numerals with different values, and both are
#    8". The message does not name the opening; the inversion is the one opening at tag 8 whose
#    guard the projections do not turn into a reflexivity, which is read off the code, not the run.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
LANGUAGE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Language.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/bounded-class.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-without-the-witness-apart" >> "$LOG"
"$P" "$TRUTH" '      s"(~(($witness) = ($index)) /\\ " +' '      s"(" +' -- \
  "$P" "$TRUTH" '        "(~(z = i) /\\ ((?j:num.' '        "(((?j:num.' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-without-the-witness-apart" >> "$LOG"

echo "################ 2-every-universal-bounded" >> "$LOG"
"$P" "$TRUTH" '      "F)))"' '      "T)))"' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-every-universal-bounded" >> "$LOG"

echo "################ 3-no-walk-through-nested-codes" >> "$LOG"
"$P" "$LANGUAGE" '                    case Some((tag, payload)) if occurs(payload) =>' \
  '                    case Some((tag, payload)) if false =>' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-no-walk-through-nested-codes" >> "$LOG"

echo "################ 4-one-tag-decided-by-tags" >> "$LOG"
"$P" "$LANGUAGE" '        case Some((App(App(_, leftTag), _), App(App(_, rightTag), _))) if leftTag == rightTag =>' \
  '        case Some((App(App(_, leftTag), _), App(App(_, rightTag), _))) if false =>' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-one-tag-decided-by-tags" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
