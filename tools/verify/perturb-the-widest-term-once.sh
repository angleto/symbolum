#!/bin/sh
# Fire the guard over the widest measured term at the defect it was written for, card 93e7bc97.
#
# What is guarded is that `7709`, the maximum an instrumented `repeatConv` recorded over one
# whole-suite run, has ONE declaration -- `Rewrite.WidestMeasured` -- and that the single copy
# which cannot cite a Scala name, the sentence in `docs/adr/0037`, is spelled from it. Before
# 2026-09-22 the figure was written by hand in four files and nothing compared any two of them;
# the one copy that did anything, `RewriteSpec`'s, entered the relation `DefaultCeiling >= 8 *`
# and `<= 16 *`, which a drifted maximum can satisfy while saying something false.
#
# Each perturbation below takes away one thing the guard rests on and `RewriteSpec` must go red.
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-22, on the tree that landed this. Control green at 33 tests; all four
# red at 32 of 33, each on the new assertion and on no other; every restore verified clean.
#
#   1. The record's sentence moved to 9999: `...0037....md must carry the maximum as 7709`, with
#      the whole flowed document printed under it, so the failure names the file to edit.
#   2. The declaration moved to 5000, which the relation still admits. **The assertion that
#      existed before this card stayed green** -- `should stand in a measured relation` passed in
#      the same run -- and only the comparison with the record went red. That is the measurement
#      that says this guard is not a second copy of the old one: the old one reads `65536` against
#      `8 *` and `16 *` and is blind to the maximum being wrong anywhere inside that band.
#   3. A copy grown back in `Induct`'s docstring: `Induct.scala writes 7709 1x, and the
#      declaration is the only one allowed: 1 was not equal to 0`.
#   4. The record read under a name nothing carries: `java.nio.file.NoSuchFileException`, red and
#      not green. An assertion that a document CONTAINS a sentence would otherwise report a
#      missing file and a disagreeing file identically, and the second is the one that matters.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

REWRITE=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rewrite.scala
INDUCT=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Induct.scala
SPEC=modules/logic/src/test/scala/garden/xeno/symbolum/logic/RewriteSpec.scala
RECORD=docs/adr/0037-the-rewriter-bounds-the-term-and-not-only-the-steps.md
SPECS='logic/testOnly garden.xeno.symbolum.logic.RewriteSpec'
LOG="$OUT/the-widest-term-once.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The record's copy drifted. This is the defect as it actually happens: somebody edits the
# sentence in the decision record, or re-measures and updates one place. Nothing in the tree could
# see it before, which was measured by putting 9999 here and watching the three document gates
# stay green over 64 tests.
echo "################ 1-the-record-drifted" >> "$LOG"
"$P" "$RECORD" \
  '**The widest term anything in this repository carries is 7709 nodes.**' \
  '**The widest term anything in this repository carries is 9999 nodes.**' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 1-the-record-drifted" >> "$LOG"

# 2. The DECLARATION moved and the record did not follow, at a value the relation still admits.
# This is the sharp one: 5000 keeps `65536 >= 8 * it` and `<= 16 * it` both true, so the assertion
# that was there before this card cannot see it, and only the comparison with the record can.
echo "################ 2-the-declaration-moved-inside-the-relation" >> "$LOG"
"$P" "$REWRITE" \
  '  val WidestMeasured: Int = 7709' \
  '  val WidestMeasured: Int = 5000' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 2-the-declaration-moved-inside-the-relation" >> "$LOG"

# 3. A second copy grown back in a docstring. Removing three copies does not stop a fourth being
# written, and a docstring is where every one of the three lived; what stops it is the count of
# the digits in the file being asserted rather than the citation being asserted.
echo "################ 3-a-copy-grown-back-in-a-docstring" >> "$LOG"
"$P" "$INDUCT" \
  '   * widest rewriting in the repository: `Rewrite.WidestMeasured` is the node count, measured over' \
  '   * widest rewriting in the repository: 7709 nodes is the count, measured over' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 3-a-copy-grown-back-in-a-docstring" >> "$LOG"

# 4. The instrument pointed at a file that is not there. An assertion that a document CONTAINS a
# sentence is a positive over a read, and a read that returns nothing reports the same absence as
# a document that disagrees; this says which, and it is the reason the test carries a negative
# control beside the positive one. It must go red rather than green.
echo "################ 4-the-record-not-read" >> "$LOG"
"$P" "$SPEC" \
  '    val record = "docs/adr/0037-the-rewriter-bounds-the-term-and-not-only-the-steps.md"' \
  '    val record = "docs/adr/0037-a-record-under-a-name-nothing-carries.md"' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 4-the-record-not-read" >> "$LOG"

echo "log: $LOG"
