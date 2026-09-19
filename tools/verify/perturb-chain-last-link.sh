#!/bin/sh
# Fire the guard of card 1358bd5e (a binding of `Chain.construct` claiming to be the last link) at
# the defect it is written for, and at the one case it deliberately does not cover.
#
# The defect: four comments in `Chain.scala` said their link was the last one while `widest` read
# `inclusion`. `matrix`'s field docstring said it with no date at all; `numbering`, `provability`
# and `transcendental` each said "The last link since <date>", the first two with the SAME date on
# two different bindings, so at most one of that pair was ever true and neither said what the last
# link is now. All four were green under every gate that exists, because `DocumentationSpec`'s
# `widest` guard holds the `widest` claim and says in writing that a positional "is last" has no
# shape it can separate from prose.
#
# Reproduced 2026-09-19 in /Users/angelo/data/WORK/symbolum-wt/chain-last-link.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}
cd "$WT" || exit 2

CHAIN=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Chain.scala
ONLY='tactics/testOnly garden.xeno.symbolum.tactics.DocumentationSpec'

./tools/sbt -batch "$ONLY" > "$OUT/0-control.log" 2>&1
echo "control exit $? (0 is the expected outcome)"
grep -E "Tests: " "$OUT/0-control.log"

# 1. `transcendental`'s sentence put back exactly as it stood until 2026-09-19. Its whole comment
#    block then carries no `was`, no `until` and no quoted `read`, which is what the guard reads.
"$P" "$CHAIN" \
  '      // Landed 2026-09-15 and was the last link until `concatenation` went on top of it the next
      // day, which the binding below says of itself. It is the only one that needs a limit, and
      // this read "The last link since 2026-09-15" until 2026-09-19. `docs/adr/0017` is the' \
  '      // The last link since 2026-09-15, and the only one that needs a limit. `docs/adr/0017` is the' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/1-transcendental.log" 2>&1
echo "1 transcendental: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/1-transcendental.log"

# 2. The floor, which is the half no defect in `Chain.scala` can show: a block scan that stopped
#    matching reports no claim at all and reads exactly like a file with none.
#
#    The perturbation is on the SPEC and not on `Chain.scala`, and the first attempt at this was
#    wrong in a way worth keeping: renaming `def construct` in the source does make the scan read
#    nothing, and it also makes `theories` fail to compile, because line 384 calls it. The run came
#    back exit 1 with no assertion in it at all, which looks like the floor firing and is not. What
#    the guard slices on is a method name the compiler needs, so the only way to starve the scan
#    without breaking the build is to move the slice.
"$P" modules/tactics/src/test/scala/garden/xeno/symbolum/tactics/DocumentationSpec.scala \
  'val body = chain.split("""def construct\\(""").drop(1).mkString' \
  'val body = chain.split("""def assemble\\(""").drop(1).mkString' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/2-scan-reads-nothing.log" 2>&1
echo "2 scan reads nothing: exit $? (1 is the expected outcome: the FLOOR fired, not the ban)"
grep -E "Tests: |\*\*\* FAILED|no longer parses|was not greater than|perturb:" "$OUT/2-scan-reads-nothing.log"

# 3. THE CASE THIS GUARD DOES NOT COVER, run so that the gap is a measurement and not a claim.
#    `matrix`'s defect is in a FIELD DOCSTRING, above `def construct`, which the guard does not
#    read. Putting the original sentence back must leave the suite GREEN. A 0 here is the expected
#    outcome and it is the honest half of this harness: the four-fifths of the population inside
#    `construct` are guarded and this fifth is not.
"$P" "$CHAIN" \
  '   * Two-by-two real matrices, appended to the chain where the five were moved into it.' \
  '   * Two-by-two real matrices, and the last link rather than one of the five.' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/3-field-docstring-uncovered.log" 2>&1
echo "3 field docstring, uncovered: exit $? (0 is the EXPECTED outcome: nothing guards this class)"
grep -E "Tests: |\*\*\* FAILED|perturb:" "$OUT/3-field-docstring-uncovered.log"
