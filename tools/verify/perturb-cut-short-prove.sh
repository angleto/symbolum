#!/bin/sh
# Fire the two witness assertions of card 011218be at the defect they were written for.
#
# The defect is the one `docs/adr/0023` recorded and left: at the propositional address a goal that
# the free route was CUT SHORT on falls to the classical procedure and comes back as a theorem at
# one axiom, indistinguishable from a goal the free route decided against. The repair reports it in
# the type, as `Prove.Outcome.CutShort`.
#
# The perturbation restores the collapse in one place: the fall to the classical procedure stops
# reading the refusal and answers `Settled` whatever stopped the free route. What must go red is the
# 128-link witness; what must stay green is the 127-link one, the counts, and everything else.
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

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
