#!/bin/sh
# Fire the two claims FRACTRAN's certifier makes about its own refusals, card f1c1bb41.
#
# `Fractran.certifyTrace` is handed a trace and answers with a theorem or a refusal. The claim in
# `docs/adr/0054` is that a wrong trace is refused by the KERNEL, and that the interpreter
# proposing the trace is believed by nothing. `FractranSpec` asserts the refusals, and an assertion
# over a refusal cannot say whose refusal it was: the Scala walk checks the landing value before it
# asks the kernel anything, so the spec would pass on that check alone.
#
# The two perturbations take the Scala half away, one at a time.
#
#   1. The check on the landing value is removed, so the walk asks the kernel to certify whatever
#      value the trace names. The spec is expected to stay GREEN: the refusal of `6, 9` under
#      `5/3, 3/2` survives, which is what says it was never the check's.
#   2. The interpreter is told that `5/3` does not apply where it does. The spec is expected to go
#      RED at the control `6, 10`: a trace the interpreter misreads cannot be certified, because
#      there is no nonzero remainder of 30 by 3 to prove.
#
# WHAT WAS SEEN, 2026-09-26, this script through sbt at 4a86b323. Control green at 10 tests,
# restore verified clean after each run.
#
#   1. Green at 10 tests, exit 0, as predicted: the refusal of `6, 9` survives without the check.
#      Run by hand with scala-cli the same afternoon, the refusal read `modus ponens on an
#      equation`: the theorem at hand said `10 = NUM_DIV (6 * 5) 3` and the one asked for said `9`.
#   2. Red at 9 of 10, exit 1, as predicted, and at the control named above: `unexpected
#      refusal: expected a value below 0, and 0 is not one`, the remainder of 30 by 3, which
#      `Digits.below` will not put above zero.
#
# ADDED BY THE VERIFICATION, 2026-09-27. Every run now takes `FractranSemanticsSpec` beside
# `FractranSpec`, so the counts above are FractranSpec's alone, and there is a third perturbation:
#
#   3. The interpreter proposes the LAST fraction that applies rather than the first. Expected RED,
#      and red by refusal: the kernel is asked for steps the definition does not make.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Fractran.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.FractranSpec garden.xeno.symbolum.theories.FractranSemanticsSpec'

echo "################ 0-control" >> "$OUT/fractran.log"
./tools/sbt -batch "$SPEC" >> "$OUT/fractran.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/fractran.log"

# 1. Expected green. The walk no longer compares where the first fraction lands with the value
# the trace names, so every landing is put to the kernel as the trace wrote it.
echo "################ 1-no-landing-check" >> "$OUT/fractran.log"
"$P" "$SOURCE" \
  'case Landed(_, p, q) if n * p / q == m => Right((p, q))' \
  'case Landed(_, p, q) if true => Right((p, q))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/fractran.log" 2>&1
echo "### exit $? for 1-no-landing-check" >> "$OUT/fractran.log"

# 2. Expected red. The walk passes over `5/3` wherever it would apply, so it asks the kernel for
# a nonzero remainder that does not exist.
echo "################ 2-a-fraction-misread" >> "$OUT/fractran.log"
"$P" "$SOURCE" \
  'if (q != 0 && (n * p) % q == 0)' \
  'if (q != 0 && (n * p) % q == 0 && !(p == 5 && q == 3))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/fractran.log" 2>&1
echo "### exit $? for 2-a-fraction-misread" >> "$OUT/fractran.log"

# 3. Expected red. The interpreter proposes the last applicable fraction rather than the first,
# which reads "first" as an order the fold does not have.
echo "################ 3-last-not-first" >> "$OUT/fractran.log"
"$P" "$SOURCE" \
  'fractions.collectFirst { case (p, q) if q != 0' \
  'fractions.reverse.collectFirst { case (p, q) if q != 0' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/fractran.log" 2>&1
echo "### exit $? for 3-last-not-first" >> "$OUT/fractran.log"

cd "$WT" && git status --porcelain >> "$OUT/fractran.log"
