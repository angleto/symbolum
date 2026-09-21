#!/bin/sh
# Fire the one thing that separates the bounded monotone from the unbounded one, card a714187c.
#
# The two differ in their hypothesis and in nothing else, so a perturbation that swapped the
# conclusion would be caught by the printed statement and says nothing. What is worth firing at is
# the BASE: the shared induction closes an equation by reflexivity and an order by `Linarith`, and
# those are the only two lines in it that know which relation is being proved. Handed the wrong
# one, the derivation refuses at the base and the message names the relation.
#
# Red at the CHAIN, since `Series` is constructed once. The control is the run before it, in the
# same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21. Control green at 49 tests, restore verified clean.
#
#   1. RED. `expected an empty range on both sides, found 0 <= 0`, which is the equation's base
#      handed an order and saying so by name.
#   2. GREEN, which is what this harness exists to have found out. `Linarith` settles `0 = 0`, so
#      for PROVABILITY the two closers are interchangeable and the parameter buys nothing in that
#      direction. What it buys is STRICTNESS: `Kernel.refl` refuses any base the rewriting did not
#      already close, where `Linarith` would accept a true equation it had failed to reduce. That
#      is the argument for keeping the equation's own closer, and it is an argument about what the
#      derivation refuses rather than about what it proves — which is the only kind a green
#      perturbation can leave standing.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Series.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesSpec'

echo "################ 0-control" >> "$OUT/bounded.log"
./tools/sbt -batch "$SPEC" >> "$OUT/bounded.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/bounded.log"

# 1. The order's base closed the equation's way. `Kernel.refl` proves `0 = 0` and the goal at the
# base of the bounded monotone is `0 <= 0`, which is not an equation at all, so the destructuring
# that reads two sides off it finds none. This is the one line in the shared induction that knows
# which relation it is proving, and it is why the base is a parameter rather than a branch.
echo "################ 1-the-order-closed-as-an-equation" >> "$OUT/bounded.log"
"$P" "$SOURCE" \
  '        MonotoneBelowStatement,
        (linarith, goal) => linarith.prove(goal))' \
  '        MonotoneBelowStatement,
        (_, goal) =>
          Term.destEq(goal) match {
            case Some((left, right)) if left == right => Right(Kernel.refl(left))
            case _ => Left(NotOfForm("an empty range on both sides", goal))
          })' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/bounded.log" 2>&1
echo "### exit $? for 1-the-order-closed-as-an-equation" >> "$OUT/bounded.log"

# 2. And the other way round, which is the half that says the parameter earns its place: the
# equation's base closed by `Linarith`. An equation between reals is two inequalities and a linear
# decider can settle `0 = 0`, so this one may well go green — and if it does, what it shows is
# that only one of the two directions is load-bearing. Read the exit code rather than assuming.
echo "################ 2-the-equation-closed-by-linarith" >> "$OUT/bounded.log"
"$P" "$SOURCE" \
  '        CongruenceBelowStatement,
        (_, goal) =>
          Term.destEq(goal) match {
            case Some((left, right)) if left == right => Right(Kernel.refl(left))
            case _ => Left(NotOfForm("an empty range on both sides", goal))
          })' \
  '        CongruenceBelowStatement,
        (linarith, goal) => linarith.prove(goal))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/bounded.log" 2>&1
echo "### exit $? for 2-the-equation-closed-by-linarith" >> "$OUT/bounded.log"

cd "$WT" && git status --porcelain >> "$OUT/bounded.log"
