#!/bin/sh
# Re-fire the guards of the radical and the cleared denominators in IDEAL (ADR 0072, 2026-11-11, no
# Mycelium card by the owner's decision) at the defects each was written for.
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
LOG="$OUT/radical.log"

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL: the same command green without a perturbation.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$THEORIES" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. No squaring asked. Expect red in IdealSpec at amc12_2000_p20, x * x = 0 and the cube, each
# refused as outside the ideal: the radical is the only thing that reaches them.
run "1-no-squarings" "$IDEAL" \
  '  val Squarings: Int = 2' \
  '  val Squarings: Int = 0' \
  -- ./tools/sbt -batch "$THEORIES"

# 2. One SQUARE_ZERO step skipped, so `D * D = 0` is handed on as though it were `D = 0`. Expect red
# in the same three, as NotRebuilt from the kernel and never as a theorem: the descent is checked,
# not trusted.
run "2-descent-short" "$IDEAL" \
  '      vanishes <- tower.init.foldRight(' \
  '      vanishes <- tower.init.drop(1).foldRight(' \
  -- ./tools/sbt -batch "$THEORIES"

echo "### all fired" >> "$LOG"
git status --porcelain >> "$LOG"
