#!/bin/sh
# Fire the guards of card 9f861d27, the irrationality of the square root of two, at their defects.
#
# `Root.SQRT_TWO_IRRATIONAL` is checked against its published text when the development is built,
# and the showcase says which of its pages the tactic surface settles. The two perturbations are
# the two ways that can drift: a statement published as something the derivation did not prove,
# and a showcase that stops carrying the sentence its neighbour says it is not.
#
# The strings are literal and were unique when this was written. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/root-two-irrational.log"
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Root.scala
SHOWCASE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Theorems.scala
ROOTSPEC='theories/testOnly garden.xeno.symbolum.theories.RootSpec'
SHOWCASESPEC='tactics/testOnly garden.xeno.symbolum.tactics.ShowcaseSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$ROOTSPEC" "$SHOWCASESPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The published statement weakened to a hypothesis the derivation did not discharge: at `q = 0`
#    the division is by zero and nothing here says what it is, so the statement is not the theorem.
# Expect red on: every test of RootSpec, the chain refusing with `SQRT_TWO_IRRATIONAL as it is written`
run "1-statement-weakened" "$SOURCE" \
  'TwoIrrational -> "!p:num q:num. 0 < q ==>' \
  'TwoIrrational -> "!p:num q:num. 0 <= q ==>' \
  -- ./tools/sbt -batch "$ROOTSPEC"

# 2. The page leaves the showcase, and the settled list still names it. Observed on its first run
#    to fail earlier than predicted here: the renamed entry is not a lemma the library holds, so
#    the test that reads each page as a published claim goes red before the counts are read.
# Expect red on: ShowcaseSpec, "publish a claim, and be the page the selection names"
run "2-page-dropped" "$SHOWCASE" \
  '    "SQRT_TWO_IRRATIONAL" ->' \
  '    "SQRT_TWO_IRRATIONAL_ABSENT" ->' \
  -- ./tools/sbt -batch "$SHOWCASESPEC"

echo "### both fired" >> "$LOG"
git status --porcelain >> "$LOG"
