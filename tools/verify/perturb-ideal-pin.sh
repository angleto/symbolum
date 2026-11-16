#!/bin/sh
# Re-fire the guards of IDEAL pinning one unknown at a time, and of a denominator the equations
# force non-zero (ADR 0079, 2026-11-12, no Mycelium card by the owner's decision) at the defects
# each was written for.
#
# The strings are literal and were unique when the work landed. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code, so a refusal means the source
# moved. Never run this beside another build of the same tree: while it runs, the tree IS the defect.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

IDEAL=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Ideal.scala
THEORIES='theories/testOnly garden.xeno.symbolum.theories.IdealSpec'
LOG="$OUT/ideal-pin.log"

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL: the same command green without a perturbation.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$THEORIES" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. No denominator forced non-zero by the equations. Expect red at mathd_algebra_362 and at the
# denominator the equations force, both refused as outside the ideal: `inv` stays an unknown.
run "1-nothing-forced" "$IDEAL" \
  '      forced = unstated.flatMap(r => forcedNonZero(known, r).flatMap(fact => inverseEquation(r, fact).toOption))' \
  '      forced = Vector.empty[(Kernel.Thm, Term, Term)]' \
  -- ./tools/sbt -batch "$THEORIES"

# 2. No unknown pinned. Expect red at mathd_algebra_362 and at the two unknowns pinned one after
# the other, whose targets have minimal polynomials of degree nine.
run "2-nothing-pinned" "$IDEAL" \
  '      case Left(outside: OutsideTheIdeal) => pinned(goal, problem, Set.empty).toRight(outside)' \
  '      case Left(outside: OutsideTheIdeal) => Left(outside)' \
  -- ./tools/sbt -batch "$THEORIES"

# 3. Unknowns of degree one taken as candidates too. Expect green: one of degree one has no root
# the order needs to pick, so the guard costs searches and not proofs. Kept to show the filter is
# an economy and not a correctness condition.
run "3-degree-one-candidates" "$IDEAL" \
  '.collect { case (i, Some(p)) if p.length > 2 => i -> p }' \
  '.collect { case (i, Some(p)) if p.length > 1 => i -> p }' \
  -- ./tools/sbt -batch "$THEORIES"

# 4. The cofactor's sign asked in normal form only. Expect red at mathd_algebra_362 and nowhere
# else: there `x * x` reduces to a multiple of `inv (y * y * y)`, and the normal form loses the
# square Linarith completes. Written as a prediction and then seen red, in a scala-cli run of
# IdealSpec over the perturbed source, before this harness ran under sbt.
run "4-normal-form-only" "$IDEAL" \
  'Vector(normal.head, Groebner.negate(normal.head), cofactor, Groebner.negate(cofactor))' \
  'Vector(normal.head, Groebner.negate(normal.head))' \
  -- ./tools/sbt -batch "$THEORIES"
