#!/bin/sh
# Fire the reals as cuts at the three choices their central arguments make, cards 709a37d4 and c71986c3.
#
# 1. The least upper bound is the union of the family's members, `\q. ?x. P x /\ dest_cut x q`.
#    Dropping `P x` makes it the union of every cut, which holds every rational and is not a cut, so
#    the construction must refuse at `CUT_COMPLETE`: this is what says the family is read at all.
# 2. `CUT_OF_RAT q` is the rationals strictly below `q`. Below or equal has a greatest element, `q`,
#    so it is not a cut, and the construction must refuse where the embedding's members are read
#    back through the characterisation.
# 3. The additive inverse below zero looks for a member `p` whose step `p + h` leaves the cut, and
#    the radius `-u - h` reflects exactly to that step. Stepping by nothing asks for `p + 0` outside
#    instead, which is not the point the radius reflects to, and the ring refuses the rearrangement
#    that would turn the escaping member into a witness.
#
# CutSpec is the spec: every fact is derived inside `Cut.construct`, so a refusal aborts the suite at
# construction, which is the red this expects. The control before must be green. Each target was
# counted before the first run and occurs once in `Cut.scala`.
#
# WHAT WAS SEEN, 2026-09-25: control green at 9 tests; all three perturbed runs aborted construction.
# 2 and 3 refused where predicted: the characterisation refused `IS_CUT (\p. RAT_LE p q)` against a
# witness for `RAT_LT`, and the ring refused `p` against `f + p`. 1 did NOT refuse where predicted.
# The prediction was that the union of every cut is refused for not being a cut; what refused was
# the first clause of the derivation, which still reads the family through `P x` and found the union
# without it. So 1 shows that the union and every use of it are one text and not two, which is
# worth having, and does not show the not-a-cut refusal, which no perturbation here reaches yet.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Cut.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CutSpec'
LOG="$OUT/cuts.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-union-of-every-cut" >> "$LOG"
"$P" "$SOURCE" \
  'read("\\q:rat. ?x:cut. P x /\\ dest_cut x q", setType)' \
  'read("\\q:rat. ?x:cut. dest_cut x q", setType)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-union-of-every-cut" >> "$LOG"

echo "################ 2-the-embedding-at-most" >> "$LOG"
"$P" "$SOURCE" \
  'mk_cut (\\p:rat. RAT_LT p q)' \
  'mk_cut (\\p:rat. RAT_LE p q)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-embedding-at-most" >> "$LOG"

echo "################ 3-the-step-by-nothing" >> "$LOG"
"$P" "$SOURCE" \
  'stepped <- plus(p, f)' \
  'stepped <- plus(p, zero)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-step-by-nothing" >> "$LOG"
