#!/bin/sh
# Fire the proofs of card 538f5094 at weakened hypotheses: Chase's Lemma 3.2 and the counted ladder
# over Gilbreath's table, `GILBREATH_BELOW` to `GILBREATH_LADDER` in `Gilbreath`.
#
# Each perturbation drops or weakens one hypothesis of one published statement, and edits the
# proof only as far as it must to assume the weaker statement, so what goes red is the first step
# that needed what was taken away. The theorems are checked by the kernel; what this shows is that
# each hypothesis is used, which a green suite does not. The control is the run before them, in
# the same tree, and it must be green. Each perturbation is a run of its own.
#
# WHAT WAS SEEN, 2026-11-11, on the tree that landed this. Control green (GilbreathSpec 7); every
# perturbation red, 0 of 7, each with "the standard chain does not build" naming the step below;
# restores verified, and the tree held only the uncommitted work after.
#
#   1. GILBREATH_SHRINK without the window bound `M k (SUC n) D`: the proof assumes only the runs,
#      and the first bound it needs on an entry of row k is refused: "expected an instance of" the
#      runs, "found" the bound `j + t0 <= SUC n ==> ...` it asked them for.
#   2. GILBREATH_BELOW with the window one shorter, `M k n D` for `M k (SUC n) D`, the proof
#      reading the window at its new width: the entry at position i + 1 is no longer inside it,
#      and `Linarith` refuses `i + 1 <= n` from `i <= n`.
#   3. GILBREATH_LADDER with the last bound `NUM_SUB D c <= 2` for `<= 1`: the closing comparison,
#      the entry at most 1 from at most `D - c`, is refused by `Linarith`. GilbreathSpec's ladder
#      reading finds this variant false, so the refusal is the right one.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Gilbreath.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.GilbreathSpec'
LOG="$OUT/gilbreath-ladder.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-shrink-without-the-window-bound" >> "$LOG"
"$P" "$FILE" '${bounded("k", "SUC n", "D")} /\\ ${runs("k", "SUC n", "D", "SUC m")}' \
  '${runs("k", "SUC n", "D", "SUC m")}' -- \
  "$P" "$FILE" 'held <- assumed(s"${bounded(K, s"SUC $N", Bd)} /\\ ${runs(K, s"SUC $N", Bd, s"SUC $Mm")}")' \
  'held <- assumed(s"${runs(K, s"SUC $N", Bd, s"SUC $Mm")}")' -- \
  "$P" "$FILE" '(wide, blocks) = (parts(0), parts(1))' '(wide, blocks) = (parts(0), parts(0))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-shrink-without-the-window-bound" >> "$LOG"

echo "################ 2-below-with-a-window-one-shorter" >> "$LOG"
"$P" "$FILE" '"GILBREATH_BELOW" -> over(s"!k:num. !n:num. !D:num. ${bounded("k", "SUC n", "D")} ==>' \
  '"GILBREATH_BELOW" -> over(s"!k:num. !n:num. !D:num. ${bounded("k", "n", "D")} ==>' -- \
  "$P" "$FILE" 'held <- assumed(bounded(K, s"SUC $N", Bd))' 'held <- assumed(bounded(K, N, Bd))' -- \
  "$P" "$FILE" 'bx <- numLinText(Seq(range._2), s"$I <= SUC $N").flatMap(c => at(h, s"$I <= SUC $N ==> $X <= $Bd")' \
  'bx <- numLinText(Seq(range._2), s"$I <= $N").flatMap(c => at(h, s"$I <= $N ==> $X <= $Bd")' -- \
  "$P" "$FILE" 'by <- numLinText(Seq(range._2), s"$I + 1 <= SUC $N").flatMap(c => at(h, s"$I + 1 <= SUC $N ==> $Y <= $Bd")' \
  'by <- numLinText(Seq(range._2), s"$I + 1 <= $N").flatMap(c => at(h, s"$I + 1 <= $N ==> $Y <= $Bd")' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-below-with-a-window-one-shorter" >> "$LOG"

echo "################ 3-ladder-stopping-at-two" >> "$LOG"
"$P" "$FILE" '/\\ NUM_SUB $bound $c <= 1"' '/\\ NUM_SUB $bound $c <= 2"' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-ladder-stopping-at-two" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
