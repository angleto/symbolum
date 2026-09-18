#!/bin/sh
# Fire the three guards of card 3f331354 at the defect they were written for.
#
# The defect is the routing `docs/adr/0023` removed: the propositional address answered by the
# fragment gate instead of by the calculus under it, so a goal with a negation in it fell through
# to the classical procedure and came back resting on the choice axiom. One perturbation reaches
# all three guards, because all three are about which procedure serves that one address.
#
# Run in a worktree of its own. perturb.sh restores on EXIT, INT and TERM and not on KILL, and
# this machine's harness has killed runs for memory; a peer reading a perturbed Prove.scala in the
# shared checkout reads code that says the opposite of what landed.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

PROVE=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Prove.scala
SPECS='garden.xeno.symbolum.tactics.PropositionalRouteSpec garden.xeno.symbolum.tactics.ProveSpec garden.xeno.symbolum.tactics.RefusalSpec'

# 0. THE CONTROL, which is the half that makes the red below mean anything: the same command, the
# same tree, no perturbation. A red under a perturbation proves nothing unless this is green.
echo "################ 0-control" >> "$OUT/perturb.log"
./tools/sbt -batch "tactics/testOnly $SPECS" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/perturb.log"

# 1. The address served by the gate again. `Minimal.prove` has the signature the calculus has, so
# this compiles and changes exactly one thing: the goals with a negation in them are turned away
# here and reach the classical procedure, at one axiom.
echo "################ 1-gate-serves-the-address" >> "$OUT/perturb.log"
"$P" "$PROVE" \
  '        intuitionistic.prove(goal) match {' \
  '        Minimal(reals.logic).prove(goal) match {' \
  -- ./tools/sbt -batch "tactics/testOnly $SPECS" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 1-gate-serves-the-address" >> "$OUT/perturb.log"

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
