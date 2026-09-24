#!/bin/sh
# Fire the guards of card a714187c's second point, the trigonometric identity, at the defects they are for.
#
# `SIN_COS_SQUARED` is proved from the two series through a second pair of Cauchy products, and
# what can go wrong is of three kinds: a series that is not the sine's while the identity is still
# claimed of it, a published statement that says something other than what was derived, and a
# general fact under the derivation that stops being derivable. Each perturbation below is one of
# those. The first and the third are caught before any test body runs, because the chain refuses
# to build; the second is caught by `TranscendentalSpec`'s statement check.
#
# What this does NOT fire is the route assertion, that the identity rests on the two Cauchy
# products and the convolution and NOT on `EXP_ADD`. No one-string edit makes the derivation go
# through the addition theorem without rewriting it, and a perturbation that rewrote the proof
# would be testing the rewrite. That assertion is a probe of the design and is recorded as such.
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

LOG="$OUT/trigonometric-identity.log"
DEFINITIONS=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Transcendental.scala
SERIES=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Series.scala
SPECS='theories/testOnly garden.xeno.symbolum.theories.TranscendentalSpec garden.xeno.symbolum.theories.SeriesSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The sine's series written with an even power, so it is no longer the sine's and the identity
#    is false of it. Predicted to be refused where the derivation joins its own spelling of the
#    series to the definition. Observed on its first run, and it is earlier than that: the chain
#    stops in `Transcendental`'s value of the sine at zero, `expected a proof of the implication's
#    antecedent`, because at an even power the series no longer stops after its first term there.
#    `SeriesSpec` builds its own `Series` and stays green, which is what it should do.
# Expect red on: TranscendentalSpec, aborted with the chain refusing to build in `Transcendental`
run "1-sine-at-an-even-power" "$DEFINITIONS" \
  '"(Power x (NUM_ADD (NUM_MUL 2 k) 1) / " +' \
  '"(Power x (NUM_MUL 2 k) / " +' \
  -- ./tools/sbt -batch "$SPECS"

# 2. A published statement that says something other than what was derived.
# Expect red on: TranscendentalSpec, "prove the statement it is published as"
run "2-statement-edited" "$DEFINITIONS" \
  'Pythagoras -> "!x:real. sin x * sin x + cos x * cos x = 1"' \
  'Pythagoras -> "!x:real. sin x * sin x - cos x * cos x = 1"' \
  -- ./tools/sbt -batch "$SPECS"

# 3. The parity split proved from the reindexing list's rules, which stall at `NUM_ADD (SUC n) n`.
# Expect red on: both specs aborted, the induction driver refusing `SUM_EVEN_ODD` with
#   `... is not equal to ...` at `NUM_ADD (SUC n) n`, observed on its first run
run "3-parity-without-the-third-rule" "$SERIES" \
  'paritywise <- prove(driver, withProd, notation, ParityStatements, recurrences ++ doubling)' \
  'paritywise <- prove(driver, withProd, notation, ParityStatements, recurrences ++ arithmetic)' \
  -- ./tools/sbt -batch "$SPECS"

echo "### all three fired" >> "$LOG"
git status --porcelain >> "$LOG"
