#!/bin/sh
# Fire the guards of E5 with the kind of task revealed and of the XOR synergy (no card: asked by
# Angelo on 2026-11-19 for the essay in `thinktank/utitlita_e_danno`, recorded in docs/adr/0063).
#
# The control is the run before them, in the same tree, and it must be green. Each perturbation is
# a run of its own, because one refusal ends the test it is in and the next would never be asked.
#
# WHAT WAS SEEN, 2026-11-19, on the tree that landed this. Control green (DecisionSpec 11, aborted
# 0); every perturbation red on its own test alone, restores verified, tree as before.
#
#   1. Refused by the closing arithmetic, decided: `84/200` and the derived value are two different
#      numbers.
#   2. The same, at the value of the bit: `14/200` against `83/200 - 7/20`.
#   3. The same, at the value of both bits: `3/4` against `1`.
#   4. Refused by `Ring` at the closing identity, not decided: `3/4` against the derived `1/2`, with
#      `inv 2` taken as an atom, so the refusal is on the fragment and not a counterexample. The
#      claim is false all the same; the instrument says only that it could not close it.
#   5. Refused by Linarith, decided: no combination of the four values gives `1 < 1/2`. Until the
#      synergy was derived from its own text, this one was refused only as a mismatch between the
#      text and a theorem built beside it, which is why the derivation now reads `Apart`.
#
# READ THE LOG, NOT THE EXIT CODE: `testOnly` over an aborted suite has exited 0 before. The
# reading is `Tests: succeeded N, failed M` with `aborted 0`, and the refusal under the failed test.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

CASE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/EssayCase.scala
XOR=modules/theories/src/test/scala/garden/xeno/symbolum/theories/EssaySynergy.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DecisionSpec'
# each perturbation runs only the test it belongs to: the whole spec is about a quarter of an hour
E5="$SPEC -- -z \"have the values it prints\""
XORT="$SPEC -- -z \"be worth nothing apart\""
LOG="$OUT/essay-revealed-xor.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The value with `tau` at phi = 1/10 one two-hundredth too high.
# 2. The value of the bit one two-hundredth too high, against values that are themselves right.
# 3. XOR with both bits worth 3/4 rather than 1.
# 4. XOR with the first bit alone worth 3/4 rather than 1/2: the piece alone would be worth something.
# 5. The synergy with the order reversed: nothing worth more than both bits.
run() {
  name=$1; test=$2; file=$3; from=$4; to=$5
  echo "################ $name" >> "$LOG"
  "$P" "$file" "$from" "$to" -- ./tools/sbt -batch "$test" >> "$LOG" 2>&1
  echo "### exit $? for $name" >> "$LOG"
}
run 1-revealed-84 "$E5" "$CASE" '$Prior $Revealing $Utility = (83:real) / 200"' '$Prior $Revealing $Utility = (84:real) / 200"'
run 2-bit-14 "$E5" "$CASE" '$Prior $Rare $Utility = (13:real) / 200"' '$Prior $Rare $Utility = (14:real) / 200"'
run 3-both-three-quarters "$XORT" "$XOR" 'Both -> "(1:real)")' 'Both -> "(3:real) / 4")'
run 4-a-alone-three-quarters "$XORT" "$XOR" 'OnlyA -> "(1:real) / 2"' 'OnlyA -> "(3:real) / 4"'
run 5-synergy-reversed "$XORT" "$XOR" 's"${value(Nothing)} < ${value(Both)}")' 's"${value(Both)} < ${value(Nothing)}")'

cd "$WT" && git status --porcelain >> "$LOG"
