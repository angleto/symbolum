#!/bin/sh
# Fire the guard added on 2026-09-20 for card 4bab95dc at the two sentences it was written for.
#
# The card's criterion is that the row naming the three absences cites the record that decided
# them, because a decided absence and an unfaced one read alike. The citation landed on 2026-09-20
# and arrived beside a justification that was false the day it was written: both cells said, in the
# present, "of the eighteen miniF2F statements this system reads and does not settle" and that two
# of them were refused by `Linarith`'s degree bound, while the completed square of `docs/adr/0032`
# had settled those two on 2026-09-18 and `ReachSpec` prints them among the proved. The repair
# deletes the count and keeps the classification; this puts each sentence back and checks the guard
# fires, once per document, because a guard that only read one of the two cells passes forever on
# the other.
#
# The control is the run before the perturbations, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SPEC='garden.xeno.symbolum.tactics.DocumentationSpec'

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it, and the perturbation tool says of itself that it does not decide whether a red is the
# right red.
echo "################ 0-control" >> "$OUT/search-absence.log"
./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/search-absence.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/search-absence.log"

# 1. The count back on the front page, in the words it carried. Expect red on:
# "The README row about proof search should hold of the search the tactics actually run"
echo "################ 1-readme-carries-the-count" >> "$OUT/search-absence.log"
"$P" README.md \
  'not one of the miniF2F statements this system reads and does not settle is a first-order search problem' \
  'of the eighteen miniF2F statements this system reads and does not settle, not one is a first-order search problem' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/search-absence.log" 2>&1
echo "### exit $? for 1-readme-carries-the-count" >> "$OUT/search-absence.log"

# 2. The second half of the same sentence, which is the one that names two statements as refused
# when the prover proves them, in the second document. Two perturbations and not one because the
# guard reads two cells and the evaluation row is the copy that was found last.
echo "################ 2-evaluation-carries-the-refusal" >> "$OUT/search-absence.log"
"$P" docs/evaluation.md \
  'two of that eighteen were one instance of `SQUARE_NONNEG` that `Linarith`'"'"'s degree bound refused' \
  'Two of them are one instance of `SQUARE_NONNEG` and are refused by `Linarith`'"'"'s degree bound, by name' \
  -- ./tools/sbt -batch "tactics/testOnly $SPEC" >> "$OUT/search-absence.log" 2>&1
echo "### exit $? for 2-evaluation-carries-the-refusal" >> "$OUT/search-absence.log"

cd "$WT" && git status --porcelain >> "$OUT/search-absence.log"
