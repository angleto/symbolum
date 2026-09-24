#!/bin/sh
# Fire the guards of card a714187c's fourth point, the square root, at the defects they are for.
#
# `Root` declares `sqrt` by choice and proves it exists from COMPLETENESS. What can go wrong with a
# name by choice is that it says less than the statements published about it, and what can go wrong
# with a link is that it stops being reachable from the end of the chain. Each perturbation below is
# one of those. The first two are caught before any test body runs: `Root.construct` checks every
# derived fact against the text it is published under and refuses the development otherwise, so a
# broken root is a chain that does not build rather than a theorem about something else. The third
# builds, and one assertion of `RootSpec` is all that stands in its way.
#
# What this does NOT fire is `RootSpec`'s assertion that the existence reaches no axiom but the
# reals'. No one-string edit of the derivation makes it spend choice without also breaking it, and
# a perturbation that rewrote the proof would be testing the rewrite. That assertion is a probe of
# the design rather than a guard against a defect that has happened, and it is recorded as such.
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

LOG="$OUT/square-root.log"
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Root.scala
CHAIN=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Chain.scala
SPECS='theories/testOnly garden.xeno.symbolum.theories.RootSpec garden.xeno.symbolum.theories.ChainSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The definition loses the sign. The choice then names A root rather than THE non-negative one,
#    so `0 <= sqrt x` is no longer derivable and the published `SQRT` is not what was built.
#    Observed on its first run, and it is not the refusal first predicted here: the chain stops
#    earlier than the statement check, in the read-back, with `modus ponens on an equation`,
#    because the definition no longer unfolds to the predicate the existence chose from.
# Expect red on: every test of RootSpec, the chain refusing to build in `Root`'s read-back
run "1-definition-without-the-sign" "$SOURCE" \
  'val SquareRootBody: String = "\\x:real. select (\\y:real. 0 <= y /\\ y * y = x)"' \
  'val SquareRootBody: String = "\\x:real. select (\\y:real. y * y = x)"' \
  -- ./tools/sbt -batch "$SPECS"

# 2. A published statement that says something other than what was derived.
# Expect red on: every test of RootSpec, the chain refusing with `SQRT_ONE as it is written`
run "2-statement-edited" "$SOURCE" \
  'AtOne -> "sqrt 1 = 1"' \
  'AtOne -> "sqrt 1 = 0"' \
  -- ./tools/sbt -batch "$SPECS"

# 3. The link drops out from under the chain's end: its constant is then outside the widest
#    signature. This targeted `val widest: Signature = root` when `Root` was the end; `Continuity`
#    was built over it the same day and became the end, so what can now go wrong is the link above
#    being built over the one below `Root` instead, which the chain accepts because nothing in
#    `Continuity` reads `sqrt`. Observed on its first run, 2026-09-24: `ChainSpec` goes red too, at
#    "put the arithmetic of the naturals under the sums", which reads the chain's end as well.
# Expect red on: RootSpec, "be reachable from the chain's end"; ChainSpec, the naturals under sums
run "3-not-under-the-end" "$CHAIN" \
  'continuity <- Continuity.construct(classical, reals, magnitude, root.theory, root.notation)' \
  'continuity <- Continuity.construct(classical, reals, magnitude, folding.theory, folding.notation)' \
  -- ./tools/sbt -batch "$SPECS"

echo "### all three fired" >> "$LOG"
git status --porcelain >> "$LOG"
