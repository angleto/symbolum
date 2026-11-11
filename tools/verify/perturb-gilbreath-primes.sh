#!/bin/sh
# Fire the proofs of card c30eae79 at weakened hypotheses: the passage from Gilbreath's ladder to
# the table of the primes, `GILBREATH_NORMALISED`, `GILBREATH_PRIMES_CONE` and
# `GILBREATH_PRIMES_FRONT` in `Gilbreath`.
#
# Each perturbation drops or weakens one hypothesis of one published statement, and edits the
# proof only as far as it must to assume the weaker statement, so what goes red is the first step
# that needed what was taken away. The theorems are checked by the kernel; what this shows is that
# each hypothesis is used, which a green suite does not. The control is the run before them, in
# the same tree, and it must be green. Each perturbation is a run of its own.
#
# WHAT WAS SEEN, 2026-11-11, on the tree that landed this. Control green (GilbreathSpec 10); every
# perturbation red, each with "the standard chain does not build" naming the step below; restores
# verified. The first attempt at 1 got no build slot within an hour, the queue's exit 75 and not a
# result, and 1 was run again on its own.
#
#   1. GILBREATH_NORMALISED with the second row's evenness replaced by `NUM_MOD (...) 2 < 2`, which
#      every number satisfies: the base of the induction that makes every later row even is
#      refused, "expected the fact the rewriting was to reach", that row's evenness being the fact.
#   2. GILBREATH_PRIMES_CONE without `1 <= n`, the proof asking `Linarith` for it where it read the
#      hypothesis: "no non-negative combination of the hypotheses gives" `1 <= n`, decided.
#   3. GILBREATH_PRIMES_FRONT claimed up to row R + 3: the window `k - 1 <= R` the ladder must
#      certify no longer follows from the row's range, and `Linarith` stops without evidence either
#      way; row R + 3 would need the window R + 1, which is not assumed.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Gilbreath.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.GilbreathSpec'
LOG="$OUT/gilbreath-primes.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# The evenness of the second row replaced by what every remainder modulo 2 satisfies, so the
# hypothesis keeps its shape and loses its content; the proofs read the weaker conjunct.
echo "################ 1-normalised-without-evenness" >> "$LOG"
"$P" "$FILE" 'private val EvenGaps: String = s"(!j:num. NUM_MOD ($D 1 (SUC j)) 2 = 0 /\\ 2 <= $D 1 (SUC j))"' \
  'private val EvenGaps: String = s"(!j:num. NUM_MOD ($D 1 (SUC j)) 2 < 2 /\\ 2 <= $D 1 (SUC j))"' -- \
  "$P" "$FILE" 'at(h, s"NUM_MOD ($D 1 (SUC $I)) 2 = 0 /\\ 2 <= $D 1 (SUC $I)")' \
  'at(h, s"NUM_MOD ($D 1 (SUC $I)) 2 < 2 /\\ 2 <= $D 1 (SUC $I)")' -- \
  "$P" "$FILE" 'gapA <- at(gaps, s"NUM_MOD ($D 1 (SUC ($I + 1))) 2 = 0 /\\ 2 <=' \
  'gapA <- at(gaps, s"NUM_MOD ($D 1 (SUC ($I + 1))) 2 < 2 /\\ 2 <=' -- \
  "$P" "$FILE" 'gapB <- at(gaps, s"NUM_MOD ($B) 2 = 0 /\\ 2 <= $B")' 'gapB <- at(gaps, s"NUM_MOD ($B) 2 < 2 /\\ 2 <= $B")' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-normalised-without-evenness" >> "$LOG"

# `1 <= n` dropped from the cone: the proof asks `numLin` for it instead of reading it.
echo "################ 2-cone-without-a-positive-window" >> "$LOG"
"$P" "$FILE" '/\\ r 0 = 0 /\\ w 0 = n /\\ 1 <= n ==> ${good(s"$D (SUC n) 1")}"' '/\\ r 0 = 0 /\\ w 0 = n ==> ${good(s"$D (SUC n) 1")}"' -- \
  "$P" "$FILE" '/\\ $R0 0 = 0 /\\ $W 0 = $N /\\ 1 <= $N")' '/\\ $R0 0 = 0 /\\ $W 0 = $N")' -- \
  "$P" "$FILE" 'suc <- predecessor(parts(8), N).map(_._1)' 'suc <- numLinText(Seq.empty, s"1 <= $N").flatMap(predecessor(_, N)).map(_._1)' -- \
  "$P" "$FILE" 's"$Setting /\\ ${staged(C, R0, Ln, W, Bd, F)} /\\ $R0 0 = 0 /\\ $W 0 = $prior /\\ 1 <= $prior ==>' \
  's"$Setting /\\ ${staged(C, R0, Ln, W, Bd, F)} /\\ $R0 0 = 0 /\\ $W 0 = $prior ==>' -- \
  "$P" "$FILE" 'hyp <- conjs(parts(0), parts(1), parts(2), bs(2), bs(3), bs(4), bs(0), bs(1), low)' \
  'hyp <- conjs(parts(0), parts(1), parts(2), bs(2), bs(3), bs(4), bs(0), bs(1))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-cone-without-a-positive-window" >> "$LOG"

# The front claimed one row further than the ladders reach.
echo "################ 3-front-one-row-further" >> "$LOG"
"$P" "$FILE" '(!k:num. 1 <= k /\\ k <= R + 2 ==> $D k 0 = 1)"),' '(!k:num. 1 <= k /\\ k <= R + 3 ==> $D k 0 = 1)"),' -- \
  "$P" "$FILE" 'body <- prop(s"1 <= (k:num) /\\ k <= $Top + 2 ==> $D k 0 = 1")' 'body <- prop(s"1 <= (k:num) /\\ k <= $Top + 3 ==> $D k 0 = 1")' -- \
  "$P" "$FILE" 'pre <- assumed(s"1 <= SUC $K /\\ SUC $K <= $Top + 2")' 'pre <- assumed(s"1 <= SUC $K /\\ SUC $K <= $Top + 3")' -- \
  "$P" "$FILE" 'inRange <- numLinText(Seq(positive, pre._2), s"1 <= $K /\\ $K <= $Top + 2")' \
  'inRange <- numLinText(Seq(positive, pre._2), s"1 <= $K /\\ $K <= $Top + 3")' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-front-one-row-further" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
