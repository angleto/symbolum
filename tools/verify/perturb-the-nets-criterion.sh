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
# WHAT WAS SEEN, 2026-09-22, on the tree that landed this. Control green at 14 tests, all three
# red, restore verified clean. Which test each one reddened, because it is not the same one and
# the difference is the finding:
#
#   1. The search charged one unit more than it spends. Red on the criterion itself, naming the
#      two goals that then need more than their size: `~p` and `~q` at 2 of 2. That is the guard
#      firing at exactly the defect it is for.
#   2. The net one short of 256. Red on "should come back settled", because the 127-link chain
#      needs 256 of 256 and 255 is not enough. The edge is where the record says it is rather
#      than near there.
#   3. The implication rule on the right charged nothing. Red on "should come back cut short":
#      a cheaper search settles the 128-link chain that the net should stop. **It does not redden
#      the tightness half**, which is what it was written for: the worst need over the population
#      stays at 4 and a witness stands. Charging nothing at the conjunction rule on the left was
#      tried too and does the same. So the second half of the criterion has never been seen
#      failing, and the comment beside it says so.
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

# 3. The tightness witness removed, which is what keeps the criterion from being a claim about a
# number nothing approaches. The implication rule on the right is where the goals of this
# population spend most of what they spend; charged nothing, they are answered in fewer units than
# their size and the assertion that some goal comes within one of its own size fails. The first
# half of the criterion passes throughout, which is the whole point of having the second.
echo "################ 3-nothing-approaches-the-bound" >> "$LOG"
"$P" "$CALCULUS" \
  '              search(hypotheses ++ gained(hypotheses, Vector(antecedent)), consequent, fuel - 1)' \
  '              search(hypotheses ++ gained(hypotheses, Vector(antecedent)), consequent, fuel)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-nothing-approaches-the-bound" >> "$LOG"

echo "log: $LOG"
