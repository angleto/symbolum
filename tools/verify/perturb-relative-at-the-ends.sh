#!/bin/sh
# Fire the guards of cards 6257d0da and 494ca432, the relative notions at the ends of [a, b], at the defect they are for.
#
# Both cards add a notion relative to `[a, b]` beside a two-sided one, `continuous_within` beside
# `continuous` and `derivative_within` beside `derivative`, and both keep the new notion from being
# a renaming by a derivation in a spec: `ContinuitySpec` takes on `[-1, 0]` a step it proves not
# continuous at `0`, and `IntegralSpec` detaches the textbook fundamental theorem at `abs` on
# `[0, 1]`, where the two-sided hypothesis fails at `0`. The defect those guards are for is the
# relative notion collapsing into the two-sided one. Each perturbation below makes it collapse at
# one end only, by dropping the one conjunct that keeps the nearby points inside at that end, and
# the end is the one where the guard's witness has its jump or its corner.
#
# What a red means here has to be read, not assumed. The derivations of the `_WITHIN` facts may use
# the dropped conjunct themselves, and then the chain refuses to build and every test goes red at
# once, which says the notion is load-bearing but does not isolate the guard. The log is kept so
# that the reader can tell which of the two happened.
#
# WHAT WAS SEEN, 2026-09-26, at 01a7b7f2. Perturbation 1 went red AT THE CHAIN: all three suites
# aborted with `the standard chain does not build: modus ponens on an equation`, because the
# definition no longer unfolds to the statement the derivation proves. So the definition is
# load-bearing, and the step guard in `ContinuitySpec` was NOT isolated: it never ran. Perturbation
# 2 did not run, stopped in the build queue after an hour, and the control's attempt in the same run
# was refused by the queue too: so the red of perturbation 1 is not yet set against a green on the
# same tree, and the next run of this harness is what supplies it. The
# conclusion the log supports is the same one `perturb-the-intermediate-value.sh` reaches for its
# own guards: a perturbation of the definition that kept the chain building would have to keep the
# proofs working, and dropping a conjunct does not.
#
# The strings are literal. perturb.sh REFUSES a perturbation that did not apply rather than running
# against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/relative-at-the-ends.log"
THEORIES=modules/theories/src/main/scala/garden/xeno/symbolum/theories
SPECS='theories/testOnly garden.xeno.symbolum.theories.ContinuitySpec garden.xeno.symbolum.theories.DerivativeSpec garden.xeno.symbolum.theories.IntegralSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. `continuous_within` looks right of `b`. The step `COND (0 < y) 1 0` on `[-1, 0]` jumps just
#    right of `0`, which is `b` there, so the relative notion now sees the jump.
# Expect red on: ContinuitySpec "take on [-1, 0] the step it refuses at 0", or the chain.
run "1-continuity-looks-right-of-b" "$THEORIES/Continuity.scala" \
  '(!y:real. a <= y /\\ y <= b /\\ abs (y - x) < d ==> abs (f y - f x) < e)' \
  '(!y:real. a <= y /\\ abs (y - x) < d ==> abs (f y - f x) < e)' \
  -- ./tools/sbt -batch "$SPECS"

# 2. `derivative_within` takes increments left of `a`, where `abs` on `[0, 1]` has its corner.
# Expect red on: IntegralSpec "detach the textbook form at abs on [0, 1]", or the chain.
run "2-derivative-looks-left-of-a" "$THEORIES/Derivative.scala" \
  'abs h < d /\\ a <= x + h /\\ x + h <= b ==>' \
  'abs h < d /\\ x + h <= b ==>' \
  -- ./tools/sbt -batch "$SPECS"

echo "### both ran" >> "$LOG"
git status --porcelain >> "$LOG"
