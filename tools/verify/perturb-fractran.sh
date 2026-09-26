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
# WHAT WAS SEEN, 2026-09-26, with the same two substitutions compiled by scala-cli against the
# classes of 1bcad72b rather than through this script, the sbt queue being eight builds deep.
#
#   1. Refused, by `modus ponens on an equation`: the theorem at hand said
#      `10 = NUM_DIV (6 * 5) 3` and the certification asked for `9`. The control was certified.
#   2. Refused, `expected a value below 0, and 0 is not one`: the remainder of 30 by 3, which
#      `Digits.below` will not put above zero.
#
# This script has not yet been run through sbt. Record its first run here when it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Fractran.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.FractranSpec'

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

cd "$WT" && git status --porcelain >> "$OUT/fractran.log"
