#!/bin/sh
# Fire the guards of card 61ed206b's second increment at the defects they were written for.
#
# The first increment took the census and repaired the second class. This one read the first class
# to the end, over every tracked document and every docstring of a main source, and what it found
# is written on the card with the criterion it counted by. Most of what it found was a photograph
# missing its date, and those were dated rather than guarded, because a photograph wants nothing.
# What is guarded here is the rest: a present-tense sentence restating a value the code declares or
# measures, which went stale with nothing going red. Two of them had already gone: the quartic in
# `docs/evaluation.md` said 37859 inferences while `FamilySpec` printed 29456, and perturbation 1
# puts that defect back exactly as it stood.
#
# The strings are literal and were unique when this was written. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code, so a refusal means the source
# moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/unwatched-figures.log"
FIGURES='tactics/testOnly garden.xeno.symbolum.tactics.FiguresSpec'
FAMILY='tactics/testOnly garden.xeno.symbolum.tactics.FamilySpec'
DOCUMENTATION='tactics/testOnly garden.xeno.symbolum.tactics.DocumentationSpec'
RING='theories/testOnly garden.xeno.symbolum.theories.RingCostSpec'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$P" "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same commands are green
# without it.
echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$FIGURES" "$FAMILY" "$DOCUMENTATION" "$RING" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. THE DEFECT AS IT STOOD: the quartic's cost as the document carried it until 2026-09-24.
# Expect red on: FamilySpec, "reach the degrees a person would want"
run "1-quartic-as-it-was" docs/evaluation.md \
  'and proved in 29456 inferences' \
  'and proved in 37859 inferences' \
  -- ./tools/sbt -batch "$FAMILY"

# 2. The declaration moves and the decision records do not, which is the direction the guard is for.
# Expect red on: FiguresSpec, "A constant the prose restates"
run "2-fuel-moved" modules/logic/src/main/scala/garden/xeno/symbolum/logic/Intuitionistic.scala \
  'val Fuel: Int = 256' \
  'val Fuel: Int = 300' \
  -- ./tools/sbt -batch "$FIGURES"

# 3. The record is edited and the declaration is not: the other direction, on the other constant.
# Expect red on: FiguresSpec, "A constant the prose restates"
run "3-instances-edited" docs/adr/0026-an-exhausted-free-route-is-reported-not-hidden.md \
  '`Domain.Instances`, which is 64.' \
  '`Domain.Instances`, which is 60.' \
  -- ./tools/sbt -batch "$FIGURES"

# 4. The parity the docstring argues from: a limit that is odd makes the argument false whatever
#    the sentence says, so the parity is a test of its own and this fires both. It was one
#    assertion below the sentence until the first run of this harness showed it never ran: the
#    sentence failed first and ended the test, which is the obscured assertion the first increment
#    of this card already paid for once.
# Expect red on: FiguresSpec, "A constant the prose restates" AND "The rewriting limit"
run "4-limit-made-odd" modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rewrite.scala \
  'val DefaultLimit: Int = 200' \
  'val DefaultLimit: Int = 201' \
  -- ./tools/sbt -batch "$FIGURES"

# 5. The floor lives in a shell script, which is why the guard reads the script rather than a Scala
#    name. Moving it must reach the record that decided it.
# Expect red on: FiguresSpec, "A constant the prose restates"
run "5-floor-moved" tools/coverage-delta.sh \
  'COVERAGE_DELTA_MIN:-90' \
  'COVERAGE_DELTA_MIN:-85' \
  -- ./tools/sbt -batch "$FIGURES"

# 6. The binder census in AGENTS.md, edited by one. The first version of this card added a guard
#    for it to `FiguresSpec`, and `LibrarySpec` had held one already, spelled from the library:
#    the census that chose it looked for the digits, and a guard that spells its figure has none.
#    The copy was removed the next day and this fires the guard that was there first.
#    It edited the count, `413`, until 2026-09-24, and stopped applying when the library grew:
#    a harness that names a figure the library moves goes stale with every lemma. It edits the
#    words the guard spells around the count instead, which move only when the sentence does.
# Expect red on: LibrarySpec, "say in `AGENTS.md` how wide the positional-specialisation hole is"
run "6-census-miscounted" AGENTS.md \
  'have two or more leading quantifiers and **' \
  'have three or more leading quantifiers and **' \
  -- ./tools/sbt -batch 'theories/testOnly garden.xeno.symbolum.theories.LibrarySpec'

# 7. A replayed count quoted in prose beside the generated table.
# Expect red on: FiguresSpec, "The replayed counts quoted in prose beside the table"
run "7-replay-quote-moved" docs/proving.md \
  'it cost **1757 inferences**' \
  'it cost **1758 inferences**' \
  -- ./tools/sbt -batch "$FIGURES"

# 8. The node count in the guide, which `RingCostSpec` measures and the guide quoted by hand.
# Expect red on: RingCostSpec, "A product of two numerals"
run "8-nodes-moved" docs/proving.md \
  '`12 * 12`
reached 573 nodes' \
  '`12 * 12`
reached 574 nodes' \
  -- ./tools/sbt -batch "$RING"

# 9. The trusted-base bound in a decision record that argues from it.
# Expect red on: DocumentationSpec, the trusted-base bound
run "9-bound-in-record" docs/adr/0005-a-model-is-untrusted-and-answers-only-at-a-point.md \
  'currently under 1200 lines' \
  'currently under 1300 lines' \
  -- ./tools/sbt -batch "$DOCUMENTATION"

# 10. and 11. landed in a second commit of the same increment: the two figures the first left
#    without a reason beside them, each a function of a definition rather than of the machine.
ROUTE='tactics/testOnly garden.xeno.symbolum.tactics.PropositionalRouteSpec'
ALGEBRAIC='tactics/testOnly garden.xeno.symbolum.tactics.AlgebraicSpec'

# Expect red on: PropositionalRouteSpec, "be the size `Intuitionistic`'s docstring gives it"
run "10-chain-size-edited" modules/logic/src/main/scala/garden/xeno/symbolum/logic/Intuitionistic.scala \
  'A 127-link chain is 511 nodes' \
  'A 127-link chain is 512 nodes' \
  -- ./tools/sbt -batch "$ROUTE"

# Expect red on: AlgebraicSpec, "cost what it costs, reported and not asserted"
run "11-example-digits-edited" modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Algebraic.scala \
  'confirmed to 33 digits)' \
  'confirmed to 34 digits)' \
  -- ./tools/sbt -batch "$ALGEBRAIC"

# 12. The number `docs/evaluation.md` says the project publishes about its trusted base. The
#     verification of 2026-09-24 made exactly this edit and saw `DocumentationSpec` and
#     `FiguresSpec` stay green: the census had counted it as guarded because `DocumentationSpec`
#     holds both the document's name and the digits, for other sentences.
# Expect red on: DocumentationSpec, the trusted-base bound
run "12-bound-in-the-evaluation" docs/evaluation.md \
  'its trusted base: four files under 1200 lines' \
  'its trusted base: four files under 1300 lines' \
  -- ./tools/sbt -batch "$DOCUMENTATION"

echo "### all twelve fired" >> "$LOG"
git status --porcelain >> "$LOG"
