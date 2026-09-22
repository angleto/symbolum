#!/bin/sh
# Fire the net's criterion at the shapes it was written against, card 87e74c7f.
#
# What is guarded is not the number 256. It is the RELATION the number is chosen by: the fuel a
# goal needs never exceeds the goal's own size, one for each connective and one for each atom
# occurrence, so 256 read forwards is the promise that a goal of at most 256 nodes is answered
# rather than stopped. `Intuitionistic.Fuel`'s docstring carries the sentence and
# `PropositionalRouteSpec` carries the assertion.
#
# Each perturbation below takes away one thing that claim rests on and the spec must go red. The
# control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN. Control green at 14 tests, all four red, restore verified clean, on three runs of
# 2026-09-22: the delivery's at `23288845`, the verification's at `3d2de7e9` in a checkout of its
# own, and the repair's at `ab263f8b`. Which test each one reddens, because it is not the same one
# and the difference is the finding:
#
#   1. The search charged one unit more than it spends. Red on **two** tests, 12 of 14. The
#      criterion itself, `Vector((2, (~ p)), (2, (~ q))) was not empty`, naming the two goals that
#      then need more than their size; and `should come back settled`, because one unit on every
#      goal moves the edge as surely as lowering the net does. The first is the guard firing at
#      exactly the defect it is for.
#   2. The net one short of 256. Red on `should come back settled` alone, 13 of 14, because the
#      127-link chain needs 256 of 256 and 255 is not enough. The edge is where the record says it
#      is rather than near there.
#   3. The implication rule on the right charged nothing. Red on `should come back cut short`
#      alone, 13 of 14: a cheaper search settles the 128-link chain that the net should stop.
#      **It does not redden the tightness half**, which is what it was written for: the witness
#      count falls from 26 to 20 and the assertion stands. Charging nothing at the conjunction
#      rule on the left was tried too and does the same.
#   4. The negation rule charged nothing. Red on the criterion alone, 13 of 14, `Vector() was
#      empty` at `approached should not be empty`. **This is the tightness half failing by
#      itself, and it is the only perturbation that has ever done it.**
#
# WHY 4 EXISTS AND WHY THE THREE BEFORE IT COULD NOT, which is the finding and not the fix. Each
# of those makes free a rule that the edge's chain of implications is BUILT from, so the edge
# moves and its tests go red before the tightness half can. The negation is the one rule of the
# calculus that chain never reaches. The delivery could not find it and said so in its test plan,
# asking a verifier for it by name; the verification found it and landed it here, `7d571d17`.
#
# ITEM 1 SAID ONE TEST AND HAS BEEN REWRITTEN RATHER THAN ANNOTATED. Three runs on three
# revisions read two. That is not two runs disagreeing about a tree, which would be worth keeping
# both accounts of: it is one reading of one run being wrong, and leaving the two lists side by
# side would have left a reader to pick between them. The inline comment beside perturbation 3
# said it fails the tightness half, contradicting this header on the same page, and is rewritten
# for the same reason.
#
# The third one was written twice, and the first version is worth the line it costs: it guarded
# `hypotheses.contains(goal)` with `fuel > 0`, which is already guaranteed three lines above, so
# the substitution APPLIED and changed nothing and the suite stayed green. `perturb.sh` refuses a
# substitution that does not apply and cannot refuse one that is inert, so a perturbation reading
# green is a statement about the perturbation before it is one about the guard.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

CALCULUS=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Intuitionistic.scala
SPEC='tactics/testOnly garden.xeno.symbolum.tactics.PropositionalRouteSpec'
LOG="$OUT/nets-criterion.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. A rule that stops paying for itself. The currying rule is the one whose weight argument was
# got wrong once, in the obvious way, and the class comment keeps the error: with the implication
# weighing one for itself the conjunction rule leaves the multiset weight exactly equal. Here the
# rule is made to spend NO fuel, which is the same defect seen from the driver rather than from
# the measure, and the criterion is what notices: a goal then needs more search than it has size.
echo "################ 1-a-rule-that-does-not-spend" >> "$LOG"
"$P" "$CALCULUS" \
  '  private def search(hypotheses: Vector[Term], goal: Term, fuel: Int): Either[LogicError, Kernel.Thm] =
    if (fuel <= 0) Left(BoundReached(SearchName, Fuel, Fuel, goal))' \
  '  private def search(hypotheses: Vector[Term], goal: Term, fuel: Int): Either[LogicError, Kernel.Thm] =
    if (fuel <= 1) Left(BoundReached(SearchName, Fuel, Fuel, goal))' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-a-rule-that-does-not-spend" >> "$LOG"

# 2. The net lowered under the family that saturates it. 127 links needs 256 of 256, so a net of
# 255 moves the edge by one link and the two tests that pin the edge change places. It is the
# assertion that the edge is where the record says it is, rather than somewhere near there.
echo "################ 2-the-net-one-short" >> "$LOG"
"$P" "$CALCULUS" \
  '  val Fuel: Int = 256' \
  '  val Fuel: Int = 255' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-net-one-short" >> "$LOG"

# 3. An attempt at the tightness witness that does NOT reach it, kept because the way it misses is
# the reason 4 exists. The implication rule on the right is where the goals of this population
# spend most of what they spend, so charging it nothing was expected to answer them in fewer units
# than their size and empty the witness set. It does not: the count falls from 26 to 20 and the
# assertion stands. What goes red is the EDGE, `should come back cut short`, because the 128-link
# chain this rule builds is settled by a search that has stopped paying for it. The first half of
# the criterion passes throughout.
echo "################ 3-nothing-approaches-the-bound" >> "$LOG"
"$P" "$CALCULUS" \
  '              search(hypotheses ++ gained(hypotheses, Vector(antecedent)), consequent, fuel - 1)' \
  '              search(hypotheses ++ gained(hypotheses, Vector(antecedent)), consequent, fuel)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-nothing-approaches-the-bound" >> "$LOG"

# 4. The tightness witness removed for real, which the three above could not do. Every attempt in
# the record charges nothing at a rule the 127-link chain is built from, so the edge moves and the
# edge tests go red before the tightness half does. The negation rule is the one rule of the
# calculus that chain does not use at all: charged nothing, the goals that carried the witnesses
# are answered in fewer units than their size, `approached` is empty, and the two edge tests are
# untouched. Seen 2026-09-22: red on `should be a net whose size is a statement about the goal`
# and on nothing else, `Vector() was empty` at `approached should not be empty`, 13 of 14 passing.
# Named by the assertion and not by a line, because the comment above it moves.
echo "################ 4-the-tightness-half-alone" >> "$LOG"
"$P" "$CALCULUS" \
  '              search(hypotheses ++ gained(hypotheses, Vector(proposition)), logic.falsity, fuel - 1)' \
  '              search(hypotheses ++ gained(hypotheses, Vector(proposition)), logic.falsity, fuel)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-tightness-half-alone" >> "$LOG"

echo "log: $LOG"
