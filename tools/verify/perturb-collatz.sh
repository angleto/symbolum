#!/bin/sh
# Fire the guards of card 3ed50474 (the S_2 encoding) at the defect they are written for.
#
# The delivery's claim: remove one rule from the table and the system still BUILDS -- eleven
# disjuncts become ten, fifty-five separations become forty-five -- and CollatzSpec goes red on
# two INDEPENDENT assertions. That independence is the point: the disjunct count says how many
# clauses were written, the separations say how many pairs the relation holds of, and a table
# with two rules collapsed passes the first and fails the second.
#
# Reproduced 2026-09-17 at 30a1452: "10 was not equal to 11" and "45 was not equal to 55".
#
# The other perturbation the delivery records is not here and is worth knowing: changing R1 from
# `ff. -> 0.` to `ff. -> 0f` gives a legal but unmarked word, and the CONSTRUCTION refuses,
# naming the position and the letter. There the guard is the derivation itself rather than a
# spec, so it needs no harness -- `Collatz.construct` simply does not return.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}
cd "$WT" || exit 2

"$P" \
  modules/theories/src/main/scala/garden/xeno/symbolum/theories/Collatz.scala \
  '    rule("B2", Group.AtTheHead, "/1", "/ff"),
    rule("B3", Group.AtTheHead, "/2", "/ft")' \
  '    rule("B2", Group.AtTheHead, "/1", "/ff")' \
  -- ./tools/sbt -batch \
     'theories/testOnly garden.xeno.symbolum.theories.CollatzSpec' \
  > "$OUT/collatz-perturb.log" 2>&1
echo "exit $? (1 is the expected outcome: the guards fired)"
grep -E "Tests: |\*\*\* FAILED|was not equal|perturb:" "$OUT/collatz-perturb.log"
