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
#
# RUN AGAIN 2026-09-19 at `e8f973f` from /Users/angelo/data/WORK/symbolum-wt/verify-1358bd5e, by a
# session verifying the card rather than delivering it, control green at 52. What it found:
#
#   - 1 and 3 reproduce exactly: one test red naming one block, and green for the field docstring.
#   - **2 does not run at all.** It exits 2 with "the text to replace is not in
#     DocumentationSpec.scala": the string below carries `def construct\\(` where the spec carries
#     `def construct\(`, one backslash. The refusal is the perturbation tool working. It was
#     left broken on purpose, because a harness quietly fixed by its verifier is a harness nobody
#     has seen fail, and repairing it was named as the next round's work.
#   - 4 and 5 were new then, and 4 was the finding: a claim written into a block that already
#     carries an unrelated `was` passed green.
#
# ROUND TWO, 2026-09-19, the delivery that answers that verification. Three changes:
#
#   - **2 is repaired**, one backslash, and it runs. What it asserts has not changed.
#   - **6 is new**, and it is here for one reason: the sentence floor is the only assertion round
#     two adds that nothing had been seen to fire, and 2 cannot show it because starving the whole
#     scan trips the older floor first.
#   - **4 now expects RED.** The guard reads the sentence that names the link instead of the whole
#     block, so the `was` of "the one that was never beside the chain" no longer clears a claim
#     written beside it. The bytes it substitutes are round one's; what moved is the guard. The
#     pair 4/5 stays, because 5 is what says 4's verdict comes from the sentence rather than from
#     where the scan reaches.
#
# What is NOT perturbed here, named so that the gap is not mistaken for coverage: the hole one
# clause narrower than the one 4 closed, a present-tense claim whose own sentence carries a `was`
# in a subordinate clause. It is pinned as a literal in the spec instead, since what exhibits it is
# a pattern applied to a string and that is an assertion rather than an edit to a source.
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
  'val body = chain.split("""def construct\(""").drop(1).mkString' \
  'val body = chain.split("""def assemble\(""").drop(1).mkString' \
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

# 4. THE FINDING OF ROUND ONE, and a red run since round two. The guard used to accept a block as
#    a record of a past state when the block carried `was`, `until` or a quoted `read` ANYWHERE in
#    it, and argued that this was safe inside `construct` "because a binding comment is short and
#    about one thing". Measured at `e8f973f` over the nineteen blocks it reads: TEN already carried
#    the marker, median block 401 characters, and five carried it for a reason with nothing to do
#    with the last link -- `word`, `matrix`, `rotation`, `magnitude` and `coding` -- so a claim
#    written into any of those five was invisible.
#
#    This puts `matrix`'s exact defect, present tense and dated today, into `matrix`'s own block,
#    which already says "the one that was never beside the chain". Same bytes as round one; what
#    changed is that the guard now asks for the marker in the sentence that names the link, so the
#    `was` next door no longer clears it:
"$P" "$CHAIN" \
  '      // The sixth, and the one that was never beside the chain. It needs `Product` for the type it' \
  '      // The sixth, and the last link since 2026-09-19. It was never beside the chain, and it
      // needs `Product` for the type it' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/4-claim-under-an-unrelated-marker.log" 2>&1
echo "4 claim in a block that already carries \`was\`: exit $? (1 since round two; 0 was round one)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/4-claim-under-an-unrelated-marker.log"

# 5. The control for 4, without which its green says nothing: the same sentence in a block that
#    carries no marker. Red, naming one block. So 4's green is the marker being satisfied by an
#    unrelated word and not the sentence being written somewhere the scan does not reach.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-19, and the first analysis this repository has: what a
      // sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/5-claim-with-nothing-masking-it.log" 2>&1
echo "5 claim in a block with no marker: exit $? (1 was measured: it fires where nothing masks it)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/5-claim-with-nothing-masking-it.log"

# 6. THE FLOOR THE SENTENCE UNIT NEEDS, which is a different one from 2 and is the only assertion
#    round two adds that nothing had seen fire. If the split stops splitting it hands back one
#    sentence per block, and the guard is then silently the block-level one round one delivered:
#    same green, same hole, and nobody told. 2 cannot show this -- it starves the whole scan and
#    the older floor catches it first -- so this starves the splitter alone and leaves the scan
#    intact. Red, naming the two counts.
"$P" modules/tactics/src/test/scala/garden/xeno/symbolum/tactics/DocumentationSpec.scala \
  'blocks.flatMap(block => """(?<=[.!?])\s+""".r.split(block).toVector)' \
  'blocks.flatMap(block => Vector(block))' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/6-sentence-split-starved.log" 2>&1
echo "6 sentence split starved: exit $? (1 is the expected outcome: the SENTENCE floor fired)"
grep -E "Tests: |\*\*\* FAILED|stopped splitting|perturb:" "$OUT/6-sentence-split-starved.log"
