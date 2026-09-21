#!/bin/sh
# Fire the two class witnesses at the defects they were written for, card 0e86daf7.
#
# What is being guarded is a NEGATIVE result: that `S2_PHI_COUNTED_STEP` and `S2_PHI_PLAIN_STEP`
# cannot be read on the marked words, only on the anchored ones. Nine theorems say it, each
# compared against the text it is written down as saying, so a derivation reaching some other
# claim is refused rather than believed. What no assertion over those nine can catch is the
# derivation being right for a reason it does not depend on, and that is what these fire at.
#
# Each perturbation below takes away one thing the argument rests on and the spec must go red.
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-21, on the tree that landed this (`1a2628e`). Control green at 20 tests,
# all four red at three tests each, restore verified clean. The messages are in
# `$OUT/anchored-class.log`, and each names the step that was taken away rather than collapsing
# somewhere downstream of it:
#
#   1. `expected a numeral of num, found NUM_SUB ZERO (SUC ZERO)`. The measure of a word with a
#      digit at position zero, with the fold rule for that position taken away: the right number
#      in a shape no comparison here can read. It is `countOfSuccessors` that says so and not
#      `measureIsNumeral`'s own sentence, because the count is what that check asks for first.
#      This is the state the file was in before 2026-09-21 and why the rule landed.
#   2. `expected a proof of (WORD_NTH (0/0.) (WORD_LENGTH w) = S2_F), found (... = S2_T)`. The
#      refusal offered per clause rather than per table: three of the six commutations begin with
#      `t`, and the `f` refusal cannot be applied to what those clauses produce. It is the
#      discrimination being load-bearing, and it is the clause's own `notElim` that refuses.
#   3. `expected 11 clauses, found (w1 = <t2's left> /\ w2 = <t2's right>)`. The walk told to
#      expect the eleven of `S2` over the six of `S2_COUNTED`, refusing at the last clause. The
#      count is read off the table rather than assumed, which is what a disjunction with a clause
#      left unanswered would otherwise slip past.
#   4. `expected a measure strictly below 1, found ZERO`. The comparison turned round, refused by
#      the check that the measure FALLS. What that check is for is that the direction cannot be
#      taken from whichever way the two numbers happen to lie: read the other way the theorem is
#      true, is about the same two words, and refutes nothing.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Collatz.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CollatzSpec'
LOG="$OUT/anchored-class.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The fold rule that reaches position zero. A digit there weighs `0 - 1` over a truncated
# subtraction, and the two recurrences that were in this set reduce a difference of successors
# and a subtraction of zero, neither of which that is. Both witnesses begin with a digit or have
# one at position zero after the step, so both measures stop half-evaluated without it. This is
# the only change here that is a repair rather than a guard, and it is fired to say so.
echo "################ 1-no-fold-at-position-zero" >> "$LOG"
"$P" "$SOURCE" \
  '          numbers.subAtZero,
          numbers.zeroMinus' \
  '          numbers.subAtZero' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-no-fold-at-position-zero" >> "$LOG"

# 2. The clause of the counted refusal choosing the wrong letter. Every commutation's left-hand
# side begins with `f` or with `t` and the refusal is per letter, so a walk that offers the same
# one to all six settles the three that begin with `f` and cannot settle the three that begin
# with `t`. A refusal that held for the table rather than per clause would survive this.
echo "################ 2-one-letter-for-six-clauses" >> "$LOG"
"$P" "$SOURCE" \
  '                      refusal = if (entry.left.head == F) noF else noT' \
  '                      refusal = noF' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-one-letter-for-six-clauses" >> "$LOG"

# 3. The clause count read off the wrong table. `S2_COUNTED` has six clauses and `S2` eleven, and
# the walk checks what it was told against what it finds. Without that check a disjunction with a
# clause left unanswered would be closed by the last case's proof.
echo "################ 3-eleven-clauses-for-six" >> "$LOG"
"$P" "$SOURCE" \
  '                answer <- overClauses(logic, asDisjunction, CountedRules.size) {' \
  '                answer <- overClauses(logic, asDisjunction, Rules.size) {' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-eleven-clauses-for-six" >> "$LOG"

# 4. The measure comparison turned round. The claim is that the potential FALLS across the
# uncounted step, which is what refutes the published bound; read the other way it is a true
# statement about the same two numbers and refutes nothing. Nothing in the shape assertions would
# see it, which is why the nine are compared against their texts.
echo "################ 4-the-comparison-turned-round" >> "$LOG"
"$P" "$SOURCE" \
  '        if (rightCount < leftCount) Right(())' \
  '        if (leftCount < rightCount) Right(())' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-comparison-turned-round" >> "$LOG"

echo "log: $LOG"
