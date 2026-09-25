#!/bin/sh
# Fire the graph-cost measurement of card e190268b at the two ways it could stop reading.
#
# The card asks for the size of a proof report at the FIRST quotient, because that is the first
# real number to extrapolate from and taking it at the end of the construction means taking it when
# it is expensive to act on. The measurement landed as assertions in `IntegerSpec` rather than as a
# probe, which is `docs/adr/0034`'s rule, and an assertion over a size is worth exactly as much as
# the walk under it: a subject that had stopped walking the graph would report small numbers and
# the reading would be that the construction costs nothing.
#
# So both perturbations break the walk rather than the statements, which is the direction a reader
# cannot check by looking at the spec.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, after `docs/adr/0047` moved both targets: control green at 18, both
# red. The cap at `INT_REAL_PAIR: 500 was not greater than 1000`, the floor added for exactly this;
# deduplication by equality at four tests, the carving one at `INT_REAL_PAIR: 126`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

DERIVATION=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Derivation.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.IntegerSpec'

echo "################ 0-control" >> "$OUT/graph-cost.log"
./tools/sbt -batch "$SPEC" >> "$OUT/graph-cost.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/graph-cost.log"

# 1. The count capped. A subject that reported a constant instead of a size would leave every
# sentence about the cost of a report true-looking and unfounded. Expect red on:
# "should carry the carving in every fact it replays, and read it in none", at the floor on what a
# bridge fact reads. Retargeted on 2026-09-25 by card 5a54c044, when `size` began stopping at a
# cited fact (`docs/adr/0047`) and the line it substitutes moved.
echo "################ 1-size-is-capped" >> "$OUT/graph-cost.log"
"$P" "$DERIVATION" \
  'def size(theorem: Kernel.Thm): Int = own(theorem).size' \
  'def size(theorem: Kernel.Thm): Int = own(theorem).size.min(500)' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/graph-cost.log" 2>&1
echo "### exit $? for 1-size-is-capped" >> "$OUT/graph-cost.log"

# 2. The walk deduplicating by EQUALITY instead of identity, which is the defect `walk`'s own
# docstring records as having happened: two theorems are equal when they are the same sequent, so a
# walk that folded them would stop early and report a proof of a few steps. This is the perturbation
# that says the figures in `docs/adr/0016` are about the shared graph and not about a term.
echo "################ 2-deduplicated-by-equality" >> "$OUT/graph-cost.log"
"$P" "$DERIVATION" \
  'new java.util.IdentityHashMap[Kernel.Thm, java.lang.Boolean]' \
  'new java.util.HashMap[Kernel.Thm, java.lang.Boolean]' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/graph-cost.log" 2>&1
echo "### exit $? for 2-deduplicated-by-equality" >> "$OUT/graph-cost.log"

cd "$WT" && git status --porcelain >> "$OUT/graph-cost.log"
