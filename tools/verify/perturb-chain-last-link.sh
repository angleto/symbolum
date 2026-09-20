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
# VERIFICATION OF ROUND TWO, 2026-09-19 at `e0230a0`, by a session that did not deliver it, in
# /Users/angelo/data/WORK/symbolum-wt/verify-0919. Control green at 52, and 1 through 6 all
# reproduce exactly as round two records them: 2 runs now and trips the real floor, 4 is red where
# round one had it green, 3 is green and is the uncovered class. What that leaves is one finding,
# and 7 and 8 below are it: the marker has a FOURTH alternative, `read the`, which the docstring
# above the guard does not state and which matches nothing anywhere in `Chain.scala`, so the card's
# own defect can still be written into a block the scan reaches and pass. The card went back to
# todo on it. A repair owes 7 a red and must leave 1, 4, 5, 6 and 8 red and 3 green.
#
# ROUND THREE, 2026-09-19, the delivery that answers that verification, and the only thing it
# moves is the marker: the fourth alternative is gone and the pattern is `read "|\bwas\b|\buntil\b`,
# which is the criterion the guard's own docstring states and nothing wider. Nothing else changed,
# so 1 through 6 and 8 assert what they asserted and **7 is red**, which is what the verification
# said a repair owes.
#
# What that repair did NOT rest on, because the two readings of a useless alternative delete
# different things: measured over the seven records inside `construct`, `until` is on its own the
# marker of NONE of them, since every sentence carrying it carries `was` or a quoted `read` as
# well, while a quoted `read` carries one record alone. "Nothing depends on it" would therefore
# have taken `until` and left the defect. What took `read the` is that its two words name no past
# state in any tense. That measurement is in the guard's docstring, and the pair of sentences
# pinning it is an assertion there rather than a perturbation here, for the same reason the
# subordinate-clause hole is: what exhibits it is a pattern applied to a literal.
#
# VERIFICATION OF ROUND THREE, 2026-09-19 at `66dd288`, by a session that did not deliver it, in
# /Users/angelo/data/WORK/symbolum-wt/verify-1358bd5e-r3. Control green at 52, and 1 through 8
# reproduce exactly as round three records them, 7 red where round two's verification had it
# green. Every figure of that delivery reproduces on the spec's own segmentation: 19 blocks, 50
# sentences, 7 naming the last link, `until` on its own the marker of none of the seven and a
# quoted `read` the marker of one alone. Whole suite 2474 tests, 0 failed, exit 0.
#
# What it leaves is one finding, and 9 with 10 as its control is it: the alternative that STAYED
# is blind to tense in the way the one that went was. `read "` matches a `read` followed by a
# quote in ANY tense, and this repository writes non-past ones -- `Reaching.scala` has "the second
# hypothesis has to read "does not lower"". So the card's own defect, present tense and dated
# today, written into a block carrying no marker of any kind, passes when its sentence says
# `has to read "the last"`. The docstring states the criterion as "the repaired text quoted after
# `read`" and the code applies something wider, which is the same distance between the stated
# criterion and the applied one that sent the card back on round two. The card went back to todo
# on it. A repair owes 9 a red and must leave 1, 2, 4, 5, 6, 8, 10 and 11 red with 3 green.
#
# A narrower alternative, measured here rather than proposed: all FOUR quoted records inside
# `construct` write the demonstrative in front, `[Tt]his read "`, and that pattern clears all
# seven records at no cost while firing on 9's sentence and on 7's. Whether that is the repair or
# whether the condition belongs somewhere other than the marker is the next round's decision.
#
# ROUND FOUR, 2026-09-20, the delivery that answers that verification, and it takes the narrowing
# above: the marker is `[Tt]his read "|\bwas\b|\buntil\b`. Re-measured before changing anything,
# on the spec's own segmentation: 19 blocks, 50 sentences, 7 naming the last link, and all seven
# clear the narrowed pattern, so no record was rewritten to keep passing. **9 is red.** Nothing
# else in the guard moved, so 1, 2, 4, 5, 6, 7, 8 and 10 assert what they asserted and 3 stays
# green.
#
# The two paragraphs of the guard's docstring that this round rewrote rather than patched: the one
# stating the removal criterion, which now covers both removals under it, and the one keeping the
# field docstrings out, whose written reason was still the block reading's -- a length argument
# that round two retired. What replaces it is the cost, measured with the test's own segmentation
# over the 29 doc comments before `def construct`: 137 sentences, five name the last link, four
# are records and the fifth is `deduction`'s true general sentence.
#
# VERIFICATION OF ROUND FOUR, 2026-09-20 at `8472ed95`, by a session that did not deliver it, in
# /Users/angelo/data/WORK/symbolum-wt/verify-sweep-0920. Control green at 52, and the whole suite
# green at 2489 on that line. What it leaves is one finding, and 12 with 13 as its control is it:
# the criterion round four wrote down -- an alternative must NAME A PAST -- was not applied to
# `until`, which stayed. `until` names a boundary and takes its tense from the verb beside it, so
# "stays that way until somebody puts one on top of it" is present and carries no record. The
# card's own defect, present tense, dated today, written into a block with no marker of any kind,
# passes. The card went back to todo on it. A repair owes 12 a red and must leave 1, 2, 4, 5, 6,
# 7, 8, 9, 10, 11 and 13 red with 3 green.
#
# What that repair may NOT rest on, for the reason round three's own note gives: "nothing depends
# on it alone" is the criterion that would have taken `until` and left `read "`, and round four
# rejected it. Measured here on the spec's own segmentation at `8472ed95`: of the seven records
# inside `construct`, three carry `was`, four carry `until`, four carry a demonstrative quoted
# `read`, and `until` is the marker of none of them on its own. So the population says nothing and
# the criterion has to.
#
# 11 is not a finding. Round three added two assertions and neither had been seen to fire, which
# is the standard round two set for itself when it added 6; round four adds one and it is here for
# the same reason. Putting the removed alternative back into the pattern -- the bare quoted `read`
# now, `read the` in round three -- makes the new pin red AT ITS OWN LINE, so it is a guard that
# has been observed failing. What cannot be isolated this way is the pin of the record resting on
# the quoted alternative alone: a pattern dropping that alternative fails the population assertion
# first, at an earlier line, and that pin can never be the failure a reader sees.
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

# 7. THE FINDING OF ROUND TWO'S VERIFICATION, and the reason the card went back to todo on
#    2026-09-19 for the second time. The guard accepts a sentence as a record of a past state when
#    it matches `\bwas\b|\buntil\b|read "|read the`, and the LAST of those four is not the criterion
#    the test's own docstring states, which is "`was`, `until`, or the repaired text quoted after
#    `read`". It matches any sentence containing the two words "read the", wherever they fall.
#
#    Measured at `e0230a0` over the fifty sentences the guard reads: "read the" occurs in NONE of
#    them, and in none of `Chain.scala` at all, so the alternative carries no record in this file
#    and only widens what passes. This writes the card's own defect -- present tense, dated today,
#    false -- into the `limit` block, which carries no marker of any kind, and puts "read the" in
#    the same sentence. Green then, and red since round three took the alternative out.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-19; read the record in `docs/adr/0017`. The first analysis
      // this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/7-marker-is-read-the.log" 2>&1
echo "7 claim whose sentence says \`read the\`: exit $? (1 since round three; 0 was the finding)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/7-marker-is-read-the.log"

# 8. The control for 7, without which its green says only that the scan did not reach the block.
#    The same claim, the same block, the same sentence, with "see the" in place of "read the": red,
#    naming one sentence. So 7's green is the fourth alternative of the marker and nothing else.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-19; see the record in `docs/adr/0017`. The first analysis
      // this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/8-control-for-seven.log" 2>&1
echo "8 the same claim with \`see the\`: exit $? (1 was measured: only the marker separates it from 7)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/8-control-for-seven.log"

# 9. THE FINDING OF ROUND THREE'S VERIFICATION. Round three took `read the` out of the marker
#    because its two words name no past state in any tense. The same is true of what it kept:
#    `read "` matches a `read` followed by a quote wherever it falls and in whatever tense, and
#    the repository's own prose writes non-past ones -- `Reaching.scala` has "the second
#    hypothesis has to read "does not lower"". So this writes the card's defect -- present tense,
#    dated today, false -- into the `limit` block, which carries no marker of any kind, with a
#    non-past quoted `read` in the same sentence. Measured green at `66dd288`, and red since round
#    four narrowed the alternative to `this read "`.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-19; the field above has to read "the last" for the two to
      // agree. The first analysis this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/9-quoted-read-is-not-past.log" 2>&1
echo "9 claim whose sentence has a non-past quoted \`read\`: exit $? (1 since round four; 0 was the finding)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/9-quoted-read-is-not-past.log"

# 10. The control for 9, without which its green says only that the scan did not reach the block.
#     The same claim, the same block, the same sentence, with "has to say" for "has to read": red,
#     naming one sentence. So 9's green is the quoted alternative of the marker and nothing else.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-19; the field above has to say "the last" for the two to
      // agree. The first analysis this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/10-control-for-nine.log" 2>&1
echo "10 the same claim with \`say\`: exit $? (1 was measured: only the marker separates it from 9)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/10-control-for-nine.log"

# 11. NOT A FINDING, and the observation the new assertions of rounds three and four were owed: a
#     guard seen only passing is untested, which is the reason 6 exists. This widens the marker
#     back to the bare quoted `read` that round four removed, and the pin of 9's sentence goes red
#     at its own line. The pin of the record resting on the quoted alternative alone cannot be
#     isolated this way, because dropping that alternative fails the population assertion at an
#     earlier line.
"$P" modules/tactics/src/test/scala/garden/xeno/symbolum/tactics/DocumentationSpec.scala \
  'val dated = """[Tt]his read "|\bwas\b|\buntil\b""".r' \
  'val dated = """read "|\bwas\b|\buntil\b""".r' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/11-removed-alternative-back.log" 2>&1
echo "11 the alternative removed in round four put back: exit $? (1 was measured, at the pin's own line)"
grep -E "Tests: |\*\*\* FAILED|was not equal to None|perturb:" "$OUT/11-removed-alternative-back.log"

# 12. THE FINDING OF ROUND FOUR'S VERIFICATION. Round four took the bare quoted `read` out of the
#     marker on a criterion it wrote down: an alternative must NAME A PAST. `until` does not. It
#     names a boundary and takes its tense from the verb beside it, so "stays that way until
#     somebody puts one on top of it" is present and future and carries no record in it at all.
#     This writes the card's defect -- present tense, dated today, false -- into the `limit` block,
#     which carries no marker of any kind, with a non-past `until` in the same sentence.
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-20, and it stays that way until somebody puts one on top
      // of it. The first analysis this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/12-until-is-not-past.log" 2>&1
echo "12 claim whose sentence says a non-past \`until\`: exit $? (0 is the finding: the marker cleared it)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/12-until-is-not-past.log"

# 13. The control for 12, without which its green says only that the scan did not reach the block.
#     The same claim, the same block, the same sentence, with "unless" for "until".
"$P" "$CHAIN" \
  '      // The first analysis this repository has: what a sequence of reals converges to and the value' \
  '      // The last link since 2026-09-20, and it stays that way unless somebody puts one on top
      // of it. The first analysis this repository has: what a sequence of reals converges to and the value' \
  -- ./tools/sbt -batch "$ONLY" \
  > "$OUT/13-control-for-twelve.log" 2>&1
echo "13 the same claim with \`unless\`: exit $? (1 is the expected outcome: only the marker separates it from 12)"
grep -E "Tests: |\*\*\* FAILED|claim a link is the last one|perturb:" "$OUT/13-control-for-twelve.log"
