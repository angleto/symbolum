#!/bin/sh
# Fire the guard that keeps the width bound on resolution refutations from being empty, card 01520749.
#
# The guard is the test in `PigeonholeSpec` that derives all three hypotheses of
# `RES_PHP_DERIVED_WIDTH` for a five-step refutation at `n = 1` and detaches the theorem there. A
# lower bound whose hypotheses nothing meets is true and says nothing, and every other test in the
# file would pass on it. The perturbation makes the hole clause's "every literal is one of the two"
# conjunct also demand `NUM_LT i ZERO`, in the published `Clause` and in the macro the derivation
# opens it with, so that no clause with a literal can be a hole clause. The derivation never reads
# that conjunct, so the theorem is still proved and published; what cannot go through is the
# witness, whose hole clause has two literals.
#
# Expected: exactly the non-vacuity test red, at the conjunct asking for `NUM_LT ZERO ZERO`, and the
# publication, axiom and resting-on tests green, which is the point: those three read the theorem,
# and a theorem about nothing reads exactly like one about something.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, before the first commit of this work. The build queue was full, so the
# measurement was taken with `scala-cli test` over `PigeonholeSpec` and `Pigeonhole.scala`, compiled
# against the kernel, sat, logic and theories classes of `7.0` at `71bf8cdf` copied out of a peer's
# worktree, rather than by this script's `tools/sbt` line. Control: 6 of 6 green. Perturbed: the
# non-vacuity test red with `modus ponens on an equation: ... (s (SUC (SUC ZERO))) ZERO = F /\
# NUM_LT ZERO ZERO ... is not ... (s (SUC (SUC ZERO))) ZERO = F`, the three tests reading the theorem
# green, prediction met. The same run also showed a second red, the `0 < n` test, which was a defect
# of that test's own assertion comparing a `List` of hypotheses with a `Set`, present on the
# unperturbed tree as well and repaired before the control above.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Pigeonhole.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.PigeonholeSpec'
LOG="$OUT/pigeonhole-width.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-a-hole-clause-with-no-literal" >> "$LOG"
"$P" "$SOURCE" \
  'hole("q", "h")}) /\\ s j i = F) /\\ " +' \
  'hole("q", "h")}) /\\ s j i = F /\\ NUM_LT i ZERO) /\\ " +' \
  -- "$P" "$SOURCE" \
  'hole(d, h)}) /\\ s $j i = F) /\\ " +' \
  'hole(d, h)}) /\\ s $j i = F /\\ NUM_LT i ZERO) /\\ " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-a-hole-clause-with-no-literal" >> "$LOG"

git status --porcelain -- "$SOURCE" >> "$LOG"
echo "### restore checked" >> "$LOG"
