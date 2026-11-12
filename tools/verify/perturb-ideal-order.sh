#!/bin/sh
# Re-fire the guards of the order joined to IDEAL (ADR 0075, 2026-11-12, no Mycelium card by the
# owner's decision) at the defects each was written for.
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
LOG="$OUT/ideal-order.log"

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL: the same command green without a perturbation.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$THEORIES" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. No polynomial in the difference sought past degree one. Expect red at amc12b_2002_p19,
# amc12b_2002_p7 and the two single roots, each refused as outside the ideal: their least
# polynomial has degree two.
run "1-degree-one" "$IDEAL" \
  '  val Degree: Int = 4' \
  '  val Degree: Int = 1' \
  -- ./tools/sbt -batch "$THEORIES"

# 2. Only the positive sign asked. Expect red at the root picked from below and nowhere else: its
# cofactor is negative.
run "2-one-sign" "$IDEAL" \
  '              Iterator(normal.head, Groebner.negate(normal.head))' \
  '              Iterator(normal.head)' \
  -- ./tools/sbt -batch "$THEORIES"

# 3. The order hypotheses handed to Linarith as written, as though no equation had rewritten them.
# Expect red at amc12b_2002_p7, whose sign needs (c - 2)^2 > 0 and is given only 0 < a.
run "3-unreduced" "$IDEAL" \
  '.flatMap((bound, n) => reduce(problem, bound, n))' \
  '.flatMap((bound, n) => Some(bound.fact))' \
  -- ./tools/sbt -batch "$THEORIES"

# 4. The inverse proved and then left out of the larger ideal. Expect red at every goal the order
# reaches, refused as outside the ideal: the sign is what makes the difference a member.
run "4-inverse-dropped" "$IDEAL" \
  'problem.right, problem.equations :+ equation)' \
  'problem.right, problem.equations)' \
  -- ./tools/sbt -batch "$THEORIES"

echo "### all fired" >> "$LOG"
git status --porcelain >> "$LOG"
