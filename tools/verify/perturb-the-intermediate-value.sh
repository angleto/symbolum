#!/bin/sh
# Fire the guards of card a714187c's third point, continuity and the intermediate value theorem, at the defects they are for.
#
# `Continuity` declares `continuous` and proves `INTERMEDIATE_VALUE` from COMPLETENESS. What can go
# wrong with a definition is that it stops discriminating, and what can go wrong with a published
# theorem is that it says something other than what was derived; with a link, that it stops being
# the end. Each perturbation below is one of those. `Continuity.construct` checks every derived
# fact against the text it is published under and refuses the development otherwise, so the first
# two are a chain that does not build rather than a theorem about something else.
#
# What this does NOT fire is `ContinuitySpec`'s two negative guards, the step that is not
# continuous and the theorem refuted without its hypothesis. They are derivations in the spec and
# a perturbation of the definition that kept the chain building would have to keep the theorem's
# proof working too; the first perturbation below shows that the obvious one does not.
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

LOG="$OUT/intermediate-value.log"
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Continuity.scala
CHAIN=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Chain.scala
SPECS='theories/testOnly garden.xeno.symbolum.theories.ContinuitySpec garden.xeno.symbolum.theories.ChainSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The radius loses its positivity. Then a radius of zero witnesses continuity of anything, the
#    definition stops discriminating, and the published facts are no longer what was derived.
#    Observed on its first run, and earlier than the statement check it was predicted at: the
#    chain stops in `CONTINUOUS_CONST`, `modus ponens on an equation`, because the definition no
#    longer unfolds to the statement that derivation proves.
# Expect red on: both specs aborted, the chain refusing to build in `Continuity`
run "1-radius-not-positive" "$SOURCE" \
  '"?d:real. 0 < d /\\ (!y:real. abs (y - x) < d ==> abs (f y - f x) < e)"' \
  '"?d:real. (!y:real. abs (y - x) < d ==> abs (f y - f x) < e)"' \
  -- ./tools/sbt -batch "$SPECS"

# 2. The published theorem without its continuity hypothesis, which is false: `ContinuitySpec`
#    refutes exactly this statement at a step.
# Expect red on: every test of ContinuitySpec, the chain refusing with `INTERMEDIATE_VALUE as it is written`
run "2-statement-without-continuity" "$SOURCE" \
  '"(!x:real. a <= x /\\ x <= b ==> continuous f x) ==> f a <= y ==> y <= f b ==> " +' \
  '"f a <= y ==> y <= f b ==> " +' \
  -- ./tools/sbt -batch "$SPECS"

# 3. The link stops being the end: its constant is then outside the widest signature.
# Expect red on: ChainSpec, the widest signature; ContinuitySpec, "be the chain's end"
run "3-not-the-end" "$CHAIN" \
  'val widest: Signature = continuity' \
  'val widest: Signature = root' \
  -- ./tools/sbt -batch "$SPECS"

echo "### all three fired" >> "$LOG"
git status --porcelain >> "$LOG"
