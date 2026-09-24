#!/bin/sh
# Fire the excluded middle's step count at the defects it was written for, card ad47e293.
#
# THE CARD WAS OPENED ON A FALSE READING AND THAT IS THE FIRST THING TO KNOW. It said nothing
# guarded the figure; `ClassicalSpec`'s "should be spelled from the derivations" has guarded three
# sentences of it since 2026-09-11. The card was written from `git grep 841`, and that gate SPELLS
# the number from `Derivation.size` instead of writing it, so it holds no digits and a grep for
# the digits cannot see it. What the card was right about is the half a list of sentences cannot
# have: six copies were not on the list and nothing watched them.
#
# So what is guarded here is two things, and they fail differently. The LIST, which says the
# sentences that do carry the figure carry the measured one; and the WALK added on 2026-09-22,
# which says no other source or document carries it at all.
#
# Each perturbation below takes away one of them and `ClassicalSpec` must go red. The control is
# the run before them, in the same tree, and it must be green.
#
# This file writes the figure out in the strings it substitutes, and that is the one place it is
# allowed: the walk reads `modules/` and the documents, not `tools/`, and a harness has to name the
# bytes it edits. The day the derivation moves these stop applying and `perturb.sh` refuses by
# naming the string, which is a harness going stale loudly rather than running against unperturbed
# code.
#
# WHAT WAS SEEN, 2026-09-22, on the tree that landed this. Control green at 30 tests, all four
# red at 29 of 30, every restore verified clean. Which of the two halves each one reddens, because
# that is the whole reason both exist:
#
#   1. A copy grown back in `RestsOn.scala`'s comment. Red on the WALK: `writing 841 out where the
#      derivation should be named instead: ...RestsOn.scala`. The list is untouched, because that
#      file was never on it.
#   2. The copy restored inside `Theorems.Showcase`. Red on the WALK again, naming that file. This
#      is the one the list could never have caught: nothing put a literal that a generator embeds
#      on a list of sentences, and the page it builds carries the measured count as well.
#   3. `CLAUDE.md`'s sentence drifted by one. Red on the LIST: `CLAUDE.md does not say the
#      excluded middle is 841 steps`, with the flowed document under it. The walk stays green,
#      since the file is a carrier and still holds the digits.
#   4. The walk pointed at a directory that does not exist. Red on the walk's non-vacuity half,
#      `the walk over the modules found no sources: 0 was not greater than 100`, and NOT on the
#      emptiness assertion above it, which passed with nothing read. That is the failure this
#      whole card is about seen from the inside: an absence reported by an instrument that opened
#      no file reads exactly like one reported by an instrument that opened every file.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

RESTSON=modules/theories/src/main/scala/garden/xeno/symbolum/theories/RestsOn.scala
SHOWCASE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Theorems.scala
SPEC=modules/logic/src/test/scala/garden/xeno/symbolum/logic/ClassicalSpec.scala
SPECS='logic/testOnly garden.xeno.symbolum.logic.ClassicalSpec'
LOG="$OUT/the-figure-the-code-knows.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. A copy grown back in a comment, which is the defect exactly as it happened six times: each
# was correct on the day it was written and compared with nothing, and the paragraph every session
# reads first said the figure was safe to write out. `RestsOn.scala` carried one of the six.
echo "################ 1-a-copy-grown-back-in-a-comment" >> "$LOG"
"$P" "$RESTSON" \
  '        // in `Foundational` above, and the excluded middle is **derived** from choice. The step' \
  '        // in `Foundational` above, and the excluded middle is **derived** from choice in 841 steps. The step' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 1-a-copy-grown-back-in-a-comment" >> "$LOG"

# 2. The copy restored where it did the most damage: a literal that a GENERATED page is built
# from. `TheoremsSpec` compares that page with this generator and the generator embeds the
# literal, so both sides move together; the page would have come to hold the measured count and a
# stale copy of it twenty-eight lines apart, with every gate green. Only the walk sees this.
echo "################ 2-the-copy-inside-a-generator" >> "$LOG"
"$P" "$SHOWCASE" \
  '        "here, derived from the choice operator alone, which is Diaconescu'"'"'s argument; what it " +' \
  '        "here, derived from the choice operator alone in 841 primitive steps, which is what it " +' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 2-the-copy-inside-a-generator" >> "$LOG"

# 3. A sentence on the list drifted from the derivation. This is the half that already existed,
# fired so that the two halves are seen failing apart: the list names the sentence, the walk names
# the file, and a reader meeting one of them should not have to guess which mechanism spoke.
echo "################ 3-a-listed-sentence-drifted" >> "$LOG"
"$P" CLAUDE.md \
  '   alone, in 841 steps, and three places in the repository said the opposite until `docs/adr/0009`' \
  '   alone, in 842 steps, and three places in the repository said the opposite until `docs/adr/0009`' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 3-a-listed-sentence-drifted" >> "$LOG"

# 4. The walk that reads nothing, which is the control an absence needs and the lesson of this card
# read back onto its own repair. An assertion that a figure appears NOWHERE is a claim about an
# absence, and an absence reported by an instrument that opened no file is indistinguishable from
# one reported by an instrument that opened every file. The non-vacuity half must go red alone.
echo "################ 4-the-walk-that-reads-nothing" >> "$LOG"
"$P" "$SPEC" \
  '      Vector("src/main", "src/test")' \
  '      Vector("src/nowhere")' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 4-the-walk-that-reads-nothing" >> "$LOG"

# 5 TO 9 ARE THE SECOND ROUND, 2026-09-24. The verification of the first put a copy in each of
# the places below and saw `ClassicalSpec` stay green: the walk read a list of three documents,
# and it exempted a carrier as a whole file. It now reads every document on disk and exempts the
# named sentences of a carrier, and each of 5 to 8 is one of those green runs made red.
# 9 is 4 again for the documents: the walk over them must be seen reading something.
#
# WHAT WAS SEEN, 2026-09-24, on the tree that landed the second round. Control green at 30, all
# nine red at 29 of 30 (3 at 28 on its first run, see below), every restore verified clean. 1, 2,
# 5, 6, 7 and 8 redden the walk naming the file; 3 the list; 4 the walk's non-vacuity over
# modules; 9 its non-vacuity over documents, `Vector() did not contain element "docs/numerics.md"`.
# On its first run 3 reddened the walk as well: the check that a second live sentence is found read
# `CLAUDE.md` itself, so a drifted live sentence left it nothing to find. It is built from the
# exemption entries now, so 3 is the list alone again.

# 5 and 6. A live copy in a document the list of three did not hold.
echo "################ 5-a-copy-in-a-dated-record" >> "$LOG"
"$P" "docs/adr/0009-the-classical-axioms-and-a-reason-that-was-wrong.md" \
  '# 0009. The classical axioms, and a reason that was wrong' \
  '# 0009. The classical axioms, and a reason that was wrong, in 841 steps' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 5-a-copy-in-a-dated-record" >> "$LOG"

echo "################ 6-a-copy-in-an-unlisted-document" >> "$LOG"
"$P" docs/numerics.md \
  '# Numerics' \
  '# Numerics, and the excluded middle is 841 steps' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 6-a-copy-in-an-unlisted-document" >> "$LOG"

# 7 and 8. A second live sentence inside a carrier, beside the one the list asserts.
echo "################ 7-a-second-sentence-in-claude-md" >> "$LOG"
"$P" CLAUDE.md \
  '   read a list of three documents and exempted carriers whole, and this sentence said "every other' \
  '   read a list of three documents and exempted carriers whole (841 steps), and this sentence said "every other' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 7-a-second-sentence-in-claude-md" >> "$LOG"

echo "################ 8-a-second-sentence-in-the-guide" >> "$LOG"
"$P" docs/proving.md \
  'rather than describing it, which is what makes the claim a measurement.' \
  'rather than describing it, which is what makes the claim a measurement of 841 steps.' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 8-a-second-sentence-in-the-guide" >> "$LOG"

# 9. The walk over the documents that reads nothing: it matches no file name at all.
echo "################ 9-the-document-walk-that-reads-nothing" >> "$LOG"
"$P" "$SPEC" \
  'file.getFileName.toString.endsWith(".md")' \
  'file.getFileName.toString.endsWith(".nowhere")' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 9-the-document-walk-that-reads-nothing" >> "$LOG"

echo "log: $LOG"
