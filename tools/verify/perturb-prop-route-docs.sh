#!/bin/sh
# Fire the two document guards added on 2026-09-18 at the defects they were written for.
#
# They are the repair of card 3f331354: the figures 58 and 98 stood in three documents that no test
# read, and `CLAUDE.md` named the procedure the routing had stopped using. A guard over a document
# is the kind most likely to be vacuous -- a substring that is not there fails, but a substring that
# would be there anyway asserts nothing -- so each one is fired at the sentence it is about.
#
# The control is the run before the perturbations, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SPEC='garden.xeno.symbolum.tactics.PropositionalRouteSpec'

# 1. The document carries a figure the code does not produce. One digit, in the one place the row
# spells it, which is what a hand edit or a half-done repair looks like.
echo "################ 1-readme-figure-drifts" >> "$OUT/perturb.log"
"$P" README.md \
  'on two atoms, **58** are exactly that' \
  'on two atoms, **57** are exactly that' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 1-readme-figure-drifts" >> "$OUT/perturb.log"

# 2. The front instructions name the procedure that stopped serving the address, which is exactly
# the sentence that stood from 2026-09-18 until this repair.
echo "################ 2-instructions-name-the-gate" >> "$OUT/perturb.log"
"$P" CLAUDE.md \
  'where `Intuitionistic`' \
  'where `Minimal` runs' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 2-instructions-name-the-gate" >> "$OUT/perturb.log"

cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
