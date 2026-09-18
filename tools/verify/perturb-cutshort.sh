#!/bin/sh
# Fire DomainTheorySpec at the defect the card 0b9ce0ca exists for.
#
# The defect is the collapse the card measured: `Domain.close` read the intuitionistic attempt with
# `toOption`, so an exhausted net and a genuine refusal became the same `None` and both fell to the
# classical route at `SELECT`, with nothing in the answer saying the free route had been cut short.
# The repair keeps the fall and reports it as `Verdict.CutShort`.
#
# The perturbation restores the collapse in one line: the refusal is no longer read, so `cutShort`
# is always empty and every settled claim comes back `Settled` whatever stopped the free route.
#
# The delivering session named this attack and said it had not run it, because perturb.sh restores
# on EXIT and not on KILL and this machine has killed runs. Hence a throwaway checkout.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DOMAIN=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Domain.scala
SPEC='garden.xeno.symbolum.theories.DomainTheorySpec'

echo "################ 0-control" >> "$OUT/perturb.log"
./tools/sbt -batch "theories/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/perturb.log"

echo "################ 1-exhaustion-not-read" >> "$OUT/perturb.log"
"$P" "$DOMAIN" \
  'free.left.toOption.filter(_.standing.stoppedShort).map(_.message)' \
  'None' \
  -- ./tools/sbt -batch "theories/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 1-exhaustion-not-read" >> "$OUT/perturb.log"

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
