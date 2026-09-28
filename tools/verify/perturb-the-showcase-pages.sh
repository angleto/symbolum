#!/bin/sh
# Fire the comparison that keeps docs/examples.md equal to what `Examples` renders, card fd256345.
#
# The card added an Analysis section to the showcase, and its claim is that nothing on a generated
# page is a copy: the statement, what it rests on and the counts are rendered from the theorem, and
# `ExamplesSpec` fails when the file is not what the command produces. A comparison of that kind
# passes vacuously when both sides are empty or when the region it reads is not the one edited, so
# the perturbations below edit each kind of thing a page carries and one thing it does not.
#
#   1. The hand-written table ABOVE the marker is edited: the fundamental theorem row loses a
#      half. Expected GREEN, and it is the control: the tree differs from the line only in prose
#      the spec says it does not check, so a red here means the line itself is red.
#   2. A figure on a generated page is edited by hand: the intermediate value theorem's count of
#      inferences goes up by one (its `_WITHIN` page since 2026-09-28, which is the one shown). Expected RED, at "be what the command produces".
#   3. A statement on a generated page is edited by hand: the intermediate value theorem's
#      continuity relative to [x, y] is written as the two-sided `cont`, which is what the page said
#      until 2026-09-28. Expected RED, at the same test.
#   4. The theorem changes and the page is not regenerated: `ROLLE_WITHIN` becomes `ROLLE` in
#      `Examples.Chosen`. Expected RED, at the same test, naming the command to run.
#
# WHAT WAS SEEN, 2026-09-27, this script through sbt at 7a15f023, restore verified after each run.
#
#   1. Green at 4 of 4, exit 0, as predicted: the table above the marker is not compared.
#   2. Red at 3 of 4, exit 1, at "be what the command produces", naming the command.
#   3. Red at 3 of 4, exit 1, at the same test.
#   4. Red at 3 of 4, exit 1, at the same test, after compiling the one perturbed source; the
#      difference printed is the ROLLE page against the ROLLE_WITHIN one.
#
# The targets of 2, 3 and 4 moved on 2026-09-28, when the analysis pages took their `_WITHIN`
# forms (card fd256345); the run recorded above is of the targets before that move.
#
# What 1 says is a limit rather than a defect of the spec, which says so in its own comment: the
# hand-written rows can drift from the library and nothing here goes red.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
LOG="$OUT/showcase-pages.log"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

PAGE=docs/examples.md
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Examples.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ExamplesSpec'

echo "################ 1-prose-above-the-marker" >> "$LOG"
"$P" "$PAGE" \
  '| The fundamental theorem of calculus | **here, both halves, since 2026-09-26** |' \
  '| The fundamental theorem of calculus | **here, one half, since 2026-09-26** |' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-prose-above-the-marker" >> "$LOG"

echo "################ 2-a-figure-on-a-page" >> "$LOG"
"$P" "$PAGE" \
  '45862 inferences of its own' \
  '45863 inferences of its own' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-a-figure-on-a-page" >> "$LOG"

echo "################ 3-a-statement-on-a-page" >> "$LOG"
"$P" "$PAGE" \
  '\operatorname{cont}_{[x, y]}(f, u) \right) \Rightarrow f(x) \le z' \
  '\operatorname{cont}(f, u) \right) \Rightarrow f(x) \le z' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-a-statement-on-a-page" >> "$LOG"

echo "################ 4-the-theorem-changes" >> "$LOG"
"$P" "$SOURCE" \
  '"ROLLE_WITHIN",' \
  '"ROLLE",' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-theorem-changes" >> "$LOG"
