#!/bin/sh
# Fire the guard that a series value compared only as a polynomial in an atom is not a decision, card d3fd8018.
#
# `ConvergenceSpec` says that `converges (Sum (\i. Power 0 i / real_of_num (NUM_FACT i))) 1`, true
# because the series converges to `exp 0`, is refused as `ValueUnidentified` and not as a decided
# `NotEqualTo`. The criterion is `numeric(wanted) && numeric(found)` in `Convergence.unidentified`,
# and the perturbation makes it always true, keeping `numeric` referenced so that an unused-member
# warning under -Xfatal-warnings cannot be what goes red.
#
# WHAT WAS SEEN, 2026-09-26, at `1bcad72b`, with a hand substitution rather than the tool. Control
# green. Perturbed: `ConvergenceSpec` red at exactly one test, "should not decide against a value
# it could only compare as a polynomial in an atom". Restore verified by `git diff --quiet`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Convergence.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ConvergenceSpec'
LOG="$OUT/series-value-standing.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Every NotEqualTo the comparison returns is decided again. Expected: red at the atom test only.
echo "################ 1-every-difference-decided" >> "$LOG"
"$P" "$SOURCE" \
  'case _: NotEqualTo if numeric(wanted) && numeric(found) => NotEqualTo(wanted, found)' \
  'case _: NotEqualTo if numeric(wanted) || true => NotEqualTo(wanted, found)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-every-difference-decided" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
