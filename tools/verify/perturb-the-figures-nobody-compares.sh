#!/bin/sh
# Fire the guards of card 61ed206b at the defects they were written for.
#
# The card is about figures written by hand that nothing compares with anything, and its three
# classes want three different treatments: a figure the code knows is compiled from the measurement,
# a figure from an instrumented run that no longer exists gets ONE declaration and citations spelled
# from it, and a photograph of a dated past event gets nothing at all, because repairing one deletes
# the record of how a guard came to exist.
#
# What this increment repaired is the second class, at the one pair the previous card left split.
# `docs/adr/0037`'s measurement has two numbers, the widest term carried and the goal it grew from.
# The first was named `Rewrite.WidestMeasured` on 2026-09-22; the second stayed as digits in the
# record AND in `Induct.afterRewriting`'s docstring -- inside the very sentence saying the first is
# not repeated there because a figure in four files goes stale in three.
#
# 1 TO 3 ARE THE PAIR. 4 AND 5 ARE THE TWO FIGURES THE RECORD DERIVES FROM IT, and they are the
# half worth reading. "A ratio of a hundred" and "eight and a half times the measured maximum" are
# sentences with NO DIGITS IN THEM, so no grep over the record can see that they rest on three
# constants; a guard written on the words alone goes green against a record whose numbers moved
# underneath them, and a guard written on the arithmetic alone goes green against a record whose
# words were edited out. Both are asserted, and 4 and 5 fire one each.
#
# The strings are literal and were unique at 5b202606. perturb.sh REFUSES a perturbation that did
# not apply rather than running against unperturbed code, so a refusal means the source moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

REWRITE=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rewrite.scala
INDUCT=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Induct.scala
RECORD=docs/adr/0037-the-rewriter-bounds-the-term-and-not-only-the-steps.md
ONE='logic/testOnly garden.xeno.symbolum.logic.RewriteSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$OUT/figures-nobody-compares.log"
  "$P" "$@" >> "$OUT/figures-nobody-compares.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/figures-nobody-compares.log"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it, and perturb.sh says of itself that it does not decide whether a red is the RIGHT red.
echo "################ 0-control" >> "$OUT/figures-nobody-compares.log"
./tools/sbt -batch "$ONE" >> "$OUT/figures-nobody-compares.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/figures-nobody-compares.log"

# 1. THE DOCSTRING THAT WROTE THE FIGURE OUT WHILE SAYING IT DOES NOT. Putting the digits back in
#    `Induct` is the defect exactly as it stood.
# Expect red on: RewriteSpec, "carry the goal the widest rewriting grew from"
run "1-induct-writes-the-goal" "$INDUCT" \
  'from a goal of
   * `Rewrite.WidestFromGoal` nodes.' \
  'from a goal of 77 nodes.' \
  -- ./tools/sbt -batch "$ONE"

# 2. The record's copy, which cannot cite a Scala name and readably stay a decision record, so it
#    is spelled from the constant instead. Moving the digits is what a reader editing prose does.
# Expect red on: RewriteSpec, "carry the goal the widest rewriting grew from"
run "2-record-goal-moved" "$RECORD" \
  'from a goal of 77 nodes' \
  'from a goal of 78 nodes' \
  -- ./tools/sbt -batch "$ONE"

# 3. The declaration, moved far enough that the record disagrees with it. This is the direction the
#    pair exists for: the code moves and the prose does not.
# Expect red on: RewriteSpec, "carry the goal the widest rewriting grew from"
run "3-constant-moved" "$REWRITE" \
  'val WidestFromGoal: Int = 77' \
  'val WidestFromGoal: Int = 90' \
  -- ./tools/sbt -batch "$ONE"

# 4. THE OTHER DERIVED FIGURE, and it is the one perturbation 3 cannot reach. `DefaultCeiling /
#    WidestMeasured` is 8.5 and two places call it "eight and a half"; this moves the numerator, so
#    the goal digits are untouched and only the derived test can see it. It also fires the ceiling
#    BAND assertion further up the file, which is a different claim -- the band is the decision
#    about the ceiling, this is the words the record describes it with -- and seeing both go red is
#    what says they are two assertions rather than one written twice.
#
#    PERTURBATION 3 USED TO BE THIS ONE and fired the wrong assertion, which is why the ratio lives
#    in a test of its own: the arithmetic sat in the same test as the digits above, a red assertion
#    ends its test, so moving the goal constant failed the digits comparison and the ratio below it
#    never ran. The perturbation written to exercise it was exercising perturbation 3 a second time.
# Expect red on: RewriteSpec, "derive the record's two ratios ..." AND the ceiling band test
run "4-multiple-silently-false" "$REWRITE" \
  'val DefaultCeiling: Int = 65536' \
  'val DefaultCeiling: Int = 262144' \
  -- ./tools/sbt -batch "$ONE"

# 5. THE SAME PHRASE FROM THE OTHER SIDE: the arithmetic is untouched and the words are edited out
#    of the record. A guard on the relation alone stays green here, which is why the phrase is
#    asserted too, and this is what says the pair of assertions is a pair rather than a belt and
#    braces.
# Expect red on: RewriteSpec, "derive the record's two ratios ..." and that one only
run "5-phrase-edited-out" "$RECORD" \
  'which is a ratio of a hundred' \
  'which is a large ratio' \
  -- ./tools/sbt -batch "$ONE"

echo "### all five fired" >> "$OUT/figures-nobody-compares.log"
git status --porcelain >> "$OUT/figures-nobody-compares.log"
