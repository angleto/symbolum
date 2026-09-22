#!/bin/sh
# Fire the two readings of a commutation's block at the defects they were written for, card 760409cc.
#
# What is guarded is that `Collatz.noCountedStepFrom` refuses a counted step for a word at EITHER
# end of the block: a word with no `f` and no `t` cannot supply a commutation's first letter, and
# a word with no `0`, `1` and `2` cannot supply its second. The second reading is what reaches a
# word holding a marker, which the card said wanted the enumeration of `WORD_LENGTH x` and does
# not. Both readings and the refusal for a word admitting neither must be load-bearing, and the
# way to say so is to take each away and watch the assertion that rests on it go red.
#
# Each perturbation below takes away one thing and `CollatzSpec` must go red. The control is the
# run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-22, on the tree that landed this. Control green at 22 tests; all five
# red; every restore verified clean. The two that matter are 1 and 2, because they fail on
# DIFFERENT tests and that is the whole claim:
#
#   1. Only offset zero. 21 of 22, red on `should reach a word holding a marker` alone:
#      `expected a word missing every letter at one end of a commutation, found ...S2_F...`.
#      The three class-witness tests stayed GREEN, so the word they are about needs nothing of
#      the second reading.
#   2. Only offset one. 19 of 22, red on the three class-witness tests and green on the one for
#      the second reading. `0/0.` holds a digit, so it is refused at offset one exactly as `/ff.`
#      is refused at offset zero. Neither reading subsumes the other, which is why the search is
#      over both and not a replacement of the first by the second.
#   3. The letter asked of the theory instead of parsed: `no constant named 0 in this theory`,
#      red on the second reading and green on the first, whose letters ARE constants. One line
#      decided which letters this walk could reach.
#   4. The block's length read at zero whatever the offset: `modus ponens on an equation:
#      NUM_LT (SUC ZERO) (SUC (SUC ZERO)) is not NUM_LT ZERO (SUC (SUC ZERO))`. The index the
#      entry lemma is stated at stops being the index the order bounds.
#   5. The offset taken without reading the word: 20 of 22, red on BOTH new tests, and the second
#      one is the point -- `/f0.` then picks offset zero and dies on `expected a word without
#      S2_F` instead of on the refusal that names a commutation. That assertion is what says the
#      word holding both letters is refused for being that word and not for some later reason.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

COLLATZ=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Collatz.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CollatzSpec'
LOG="$OUT/the-other-end-of-the-block.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Only the first letter read, which is the argument as it stood before this card. `/ff.` holds
# an `f`, so the offset search finds nothing and the refusal is not derivable: the test written
# for the second reading must be the one that goes red, and the witness of the anchored class,
# whose word `0/0.` holds no marker, must stay green in the same run.
echo "################ 1-only-the-first-letter-read" >> "$LOG"
"$P" "$COLLATZ" \
  '      offset <- (0 until CountedRules.map(_.left.size).minOption.getOrElse(0))' \
  '      offset <- (0 until 1)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-only-the-first-letter-read" >> "$LOG"

# 2. Only the second letter read, which is the other half of the same claim. `0/0.` holds a `0`,
# so the witness of the anchored class is the one that must go red here. The two together say
# neither reading is the general one and neither is redundant.
echo "################ 2-only-the-second-letter-read" >> "$LOG"
"$P" "$COLLATZ" \
  '      offset <- (0 until CountedRules.map(_.left.size).minOption.getOrElse(0))' \
  '      offset <- (1 until CountedRules.map(_.left.size).minOption.getOrElse(0))' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-only-the-second-letter-read" >> "$LOG"

# 3. The letter fetched from the theory instead of parsed. Three of the seven letters are numerals
# and not constants of any name, so this is the one line that decided which letters the walk could
# reach: the digits become a refusal naming a constant nobody declared, and the second reading has
# nothing to refuse with. The first reading, whose letters ARE constants, must stay green.
echo "################ 3-the-digit-asked-for-as-a-constant" >> "$LOG"
"$P" "$COLLATZ" \
  '      marker <- tools.letter(markerName)' \
  '      marker <- tools.constant(markerName, Numbers)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-digit-asked-for-as-a-constant" >> "$LOG"

# 4. The order on the block's length taken at zero whatever the offset is, which is the uniform
# `S2_RULE_NOT_EMPTY` standing in for the per-clause length. At offset one the index the entry
# lemma is stated at stops matching the index the order bounds, and the two halves no longer meet.
echo "################ 4-the-block-length-read-at-zero" >> "$LOG"
"$P" "$COLLATZ" \
  '                      belowSize <- numeralBelow(tools, offset, entry.left.size)' \
  '                      belowSize <- numeralBelow(tools, 0, entry.left.size)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-block-length-read-at-zero" >> "$LOG"

# 5. The offset taken without reading the word, which is the failure that would make the refusal
# for `/f0.` look like a derivation. A word holding a marker AND a digit is what neither reading
# reaches, and the assertion that says so is on the refusal naming a commutation: with the search
# blind, that word picks the first offset and dies further in, on a message about one letter.
echo "################ 5-the-offset-taken-without-reading-the-word" >> "$LOG"
"$P" "$COLLATZ" \
  '        .find(at => !letters.exists(countedLettersAt(at).contains))' \
  '        .find(at => at >= 0)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 5-the-offset-taken-without-reading-the-word" >> "$LOG"

echo "log: $LOG"
