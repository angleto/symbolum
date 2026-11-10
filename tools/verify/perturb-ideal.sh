#!/bin/sh
# Re-fire the guards of the IDEAL procedure (Groebner, Ideal, and its route in Prove; 2026-11-10,
# no Mycelium card by the owner's decision) at the defects each was written for.
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

GROEBNER=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Groebner.scala
ERRORS=modules/logic/src/main/scala/garden/xeno/symbolum/logic/LogicError.scala
PROVE=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Prove.scala
THEORIES='theories/testOnly garden.xeno.symbolum.theories.GroebnerSpec garden.xeno.symbolum.theories.IdealSpec'
ROUTE='tactics/testOnly garden.xeno.symbolum.tactics.IdealRouteSpec'
LOG="$OUT/ideal.log"

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL: the same two commands green without a perturbation.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$THEORIES" "$ROUTE" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. Cofactors with the wrong sign: the search claims membership with a certificate that is false.
# Expect red in GroebnerSpec (the identity property) and in IdealSpec (NotRebuilt from the kernel),
# and never a theorem: this is the perturbation that shows the kernel, not the search, is trusted.
run "1-wrong-cofactors" "$GROEBNER" \
  'Membership.Member(reduced.cofactors.map(negate), charged.spent)' \
  'Membership.Member(reduced.cofactors, charged.spent)' \
  -- ./tools/sbt -batch "$THEORIES"

# 2. "Not in the ideal" called decided, which files a true claim (x * x = 0 ==> x = 0) as settled.
# Expect red in IdealSpec: "never as decided, because it is true".
run "2-outside-decided" "$ERRORS" \
  'which says nothing about whether it holds of the reals"

  def standing: LogicError.Standing = LogicError.Standing.Unread' \
  'which says nothing about whether it holds of the reals"

  def standing: LogicError.Standing = LogicError.Standing.Decided' \
  -- ./tools/sbt -batch "$THEORIES"

# 3. The route unwired: Prove never asks IDEAL. Expect red in IdealRouteSpec's first test.
run "3-route-unwired" "$PROVE" \
  '                ideal.prove(goal) match {' \
  '                (Left(()): Either[Unit, Kernel.Thm]) match {' \
  -- ./tools/sbt -batch "$ROUTE"

# 4. IDEAL's refusal reported in place of the one RING and LINARITH gave.
# Expect red in IdealRouteSpec's second test.
run "4-refusal-taken-away" "$PROVE" \
  '                    Left(priceOf(goal).getOrElse(FromLogic(named(goal).getOrElse(fromRing))))' \
  '                    Left(FromLogic(ideal.prove(goal).left.toOption.get))' \
  -- ./tools/sbt -batch "$ROUTE"

echo "### all fired" >> "$LOG"
git status --porcelain >> "$LOG"
