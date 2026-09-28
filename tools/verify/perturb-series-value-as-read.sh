#!/bin/sh
# Fire the guard that a series value refused as NotEqualAsRead is still a decision between numbers, card 1d70cd51.
#
# Since `24faf99a` RING and FIELD say `NotEqualAsRead` when an atom of the two forms is not a free
# variable, and `inv (1 + 1)` is such an atom. `Convergence.unidentified` promotes either refusal to
# `NotEqualTo` when both values are `numeric`, and that condition is what keeps the promotion from
# deciding a false thing: two values can differ as forms and be one number.
#
# Expected, and what was seen on 2026-09-28 at `integrate-0927` `d59436fe` plus the change, both
# runs of `SeriesFragmentBoundarySpec`, 12 tests, control 12 green, restores verified by the tool:
#   1. the condition dropped: red at "A value equal to the true one only through inv 0 = 0"
#      (`2 + inv 0`, refused as Decided) and at "A value that is 2 once a reciprocal of nought is
#      read" (`2 + 1 / 0`, the same), 10 green. The prediction written before the run named the
#      first and, for the second, "A value that is 2 with every divisor placed", whose
#      `inv (inv (inv (inv 2)))` it expected to be decided; it stayed `ValueUnidentified`, because
#      its refusal is not one of the two that say the forms differ, so this condition is not what
#      guards it. In this file, what the condition guards is the two values that are 2 through `inv 0 = 0`.
#   2. the refusal it reads narrowed back to `NotEqualTo`, the code before this card: red at "A
#      value that is not 2 over a divisor LINARITH places", as at `cf853ffa`, 11 green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Convergence.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.SeriesFragmentBoundarySpec'
LOG="$OUT/series-value-as-read.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Any two differing forms are two numbers. `numeric` stays referenced, so an unused-member
# warning under -Xfatal-warnings cannot be what goes red.
echo "################ 1-condition-dropped" >> "$LOG"
"$P" "$SOURCE" \
  'if numeric(wanted) && numeric(found) => NotEqualTo(wanted, found)' \
  'if true || (numeric(wanted) && numeric(found)) => NotEqualTo(wanted, found)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-condition-dropped" >> "$LOG"

# 2. Only `NotEqualTo` is read, as before this card.
echo "################ 2-as-read-ignored" >> "$LOG"
"$P" "$SOURCE" \
  'case _: (NotEqualTo | NotEqualAsRead) if' \
  'case _: NotEqualTo if' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-as-read-ignored" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
