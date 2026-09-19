#!/bin/sh
# Fire the witness assertions of card 011218be at the two defects they were written for.
#
# The defect is the one `docs/adr/0023` recorded and left: at the propositional address a goal that
# the free route was CUT SHORT on falls to the classical procedure and comes back as a theorem at
# one axiom, indistinguishable from a goal the free route decided against.
#
# It was repaired in TWO places on two days, and each half has a perturbation here because each
# half was, on its own, a complete-looking repair with the defect still on the surface. The first
# is the type, `Prove.Outcome.CutShort`, landed 2026-09-18. The second is the page: the field it
# put on `Cost.Report` had no reader until 2026-09-19, which the verification of that day measured
# by printing the page of a 128-link chain beside the page of Peirce's law and finding them
# different in the claim and in the inference count and in nothing else.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

PROVE=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Prove.scala
SPEC='garden.xeno.symbolum.tactics.PropositionalRouteSpec'

echo "################ 0-control" >> "$OUT/perturb.log"
./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/perturb.log"

echo "################ 1-reason-not-read" >> "$OUT/perturb.log"
"$P" "$PROVE" \
  '                      Prove.Outcome.CutShort(theorem, limit, allowed)' \
  '                      Prove.Outcome.Settled(theorem)' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 1-reason-not-read" >> "$OUT/perturb.log"

# 2. The second half of the same card, found by the verification of 2026-09-18 and repaired on
# 2026-09-19: the type carried the case and the PAGE never said it, so on the surface a person
# reads a cut-short route stayed indistinguishable from a decided one. The perturbation drops the
# caveat back out of the page and leaves everything else, `Prove` included, repaired.
#
# What must go red is the CostSpec witness at 128 links; what must stay green is its control at
# 127, the rest of CostSpec, and all of PropositionalRouteSpec, which measures the floor below.
COST=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Cost.scala

echo "################ 2-caveat-not-printed" >> "$OUT/perturb.log"
./tools/sbt -batch "tactics/testOnly $SPEC garden.xeno.symbolum.tactics.CostSpec" \
  >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 2-control" >> "$OUT/perturb.log"
"$P" "$COST" \
  'Vector(head) ++ proof ++ caveat ++ charged' \
  'Vector(head) ++ proof ++ charged' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC garden.xeno.symbolum.tactics.CostSpec" \
  >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 2-caveat-not-printed" >> "$OUT/perturb.log"

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
