#!/bin/sh
# Fire ContextSpec at the defect the card b6d5470f exists for.
#
# The defect: a goal's own hypotheses are not facts, so `H ==> C` is matched whole and a lemma that
# IS the goal is refused. The repair is one line in `Prove.apply`, which asks `underHypotheses`
# after the whole goal has already been tried. Taking that line out restores the defect exactly,
# and what the card claims is asymmetric: the three witnesses go red while the structural
# assertions and the negative control stay green. A perturbation that reddens everything would
# mean the file is measuring something else.
#
# Run in a worktree of its own: perturbing `Prove.scala` in the shared checkout breaks the compile
# of anybody else building there, and perturb.sh restores on EXIT/INT/TERM but not on KILL.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

PROVE=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Prove.scala
SPECS='garden.xeno.symbolum.tactics.ContextSpec garden.xeno.symbolum.tactics.ShowcaseSpec'

# 0. THE CONTROL. A red under a perturbation means nothing unless the same command is green here.
echo "################ 0-control" >> "$OUT/perturb.log"
./tools/sbt -batch "tactics/testOnly $SPECS" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/perturb.log"

# 1. The route not asked for at all: `chained` alone, which is `Prove.apply` as it was before the
# card. The type is unchanged, so this compiles and changes exactly one thing.
echo "################ 1-route-not-asked" >> "$OUT/perturb.log"
"$P" "$PROVE" \
  'chained(goal).orElse(underHypotheses(goal)).toRight(refusal)' \
  'chained(goal).toRight(refusal)' \
  -- ./tools/sbt -batch "tactics/testOnly $SPECS" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 1-route-not-asked" >> "$OUT/perturb.log"

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
