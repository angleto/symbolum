#!/bin/sh
# Fire the both-directions guards of card db67b658 at the defect each was written for.
#
# Two halves, and the second one is the card's decision being spent. 1 to 3 are the sites in
# `modules/tactics`, which can see `Prose.count` in `theories`. 4 to 8 are the sites in the five
# modules that CANNOT see it -- `checker`, `core`, `kernel`, `mark`, `sat` -- where the decision
# was a private counter per module, and for `kernel` no counter at all but a reworded sentence,
# because the trusted base is counted and a line that exists to render English is a line
# somebody has to read and believe.
#
# The card is the half of `0da00ff8`'s class that its census could not see. Three more sites in
# `modules/tactics` interpolate a count in front of a noun carrying its plural in the literal, and
# all three can reach one: two say `agreed to 1 digits`, and the third, which the card's own list
# did not carry, says `confirmed by more than 1 digits`.
#
# WHY THE THIRD IS IN THE CLASS AND `Rules.size` IS NOT, since that is the only judgement here:
# `Relation.NotCredible` is produced exactly when `confirmed < Relation.Confirmation`, which is
# ten, and `confirmed` is a `max(0, ...)`, so the number that message prints lives in 0 to 9 and
# one is inside it. `Collatz`'s `${Rules.size} clauses` is the constant eleven and is not.
#
# Each perturbation puts ONE site back to the bare interpolation and leaves the others repaired:
# a shared helper that went singular everywhere is a different failure and would take every guard
# down at once, which is what these assertions are shaped to tell apart.
#
# SEEN RED BEFORE BEING BELIEVED. The Remedy guard failed on its first run for a reason worth
# keeping: `RaiseALimit` puts the limit and the reason in one line, so the message does not END at
# the count and an assertion written with `endWith` was wrong about the shape rather than about the
# repair. It reads `include("more than 1 digit:")` now, with the colon, because a bare
# `include("more than 1 digit")` is a substring of the defect it is meant to catch.
#
# **8 WAS GREEN ON ITS FIRST RUN AND THAT IS WHY THIS HARNESS EXISTS.** The guard it fires read
# `include("is not one of 1 step")`, which is a SUBSTRING of the defect it is written against,
# `is not one of 1 steps`, so the assertion passed with the counter taken out. It is `endWith`
# now. That is the same shape the Remedy guard was caught in, one file over, by a red run rather
# than by a perturbation: a both-directions test whose singular branch is a prefix of its own
# defect asserts nothing at all.
#
# 14 TO 17 ARE THE FOURTH INCREMENT, and three of them are a second part of speech. Re-reading the
# census to the end again found `ArityMismatch` in `kernel`, which says `takes 1 arguments` at
# every unary type operator, and `GrewPastCeiling`, whose sentence is written twice -- once in
# `logic` and once by `Remedy` one module up -- and whose BOTH numbers reach one, the ceiling being
# a parameter and the guard being `width > ceiling`.
#
# And it found what a counter does not reach. `1 argument were given` survived increment three in
# `LogicError`, whose own spec asserted that sentence: `Plural` repaired the noun, nothing agrees a
# verb with a number, and a test copied from the message it guards cannot tell the two apart. 16
# fires at that verb, and it is the one perturbation here whose defect was in the tree with a
# green suite over it for two days.
#
# The strings are literal and were unique at 372a025, and 14 to 20 at b2091a03. perturb.sh REFUSES
# a perturbation that did not apply rather than running against unperturbed code, so a refusal
# means the source moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LEDGER=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Ledger.scala
PARSE=modules/checker/src/main/scala/garden/xeno/symbolum/checker/Parse.scala
PERRON=modules/core/src/main/scala/garden/xeno/symbolum/Perron.scala
TERM=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Term.scala
MARK=modules/mark/src/main/scala/garden/xeno/symbolum/mark/Mark.scala
RESOLUTION=modules/sat/src/main/scala/garden/xeno/symbolum/sat/Resolution.scala
SOLVER=modules/sat/src/main/scala/garden/xeno/symbolum/sat/Solver.scala
RELATION=modules/core/src/main/scala/garden/xeno/symbolum/Relation.scala
LOGICERROR=modules/logic/src/main/scala/garden/xeno/symbolum/logic/LogicError.scala
VALUE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Value.scala
REMEDY=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Remedy.scala
KERNELERROR=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/KernelError.scala
BOTH='tactics/testOnly garden.xeno.symbolum.tactics.LedgerSpec garden.xeno.symbolum.tactics.RemedySpec'

run() { n="$1"; shift
  echo "################ $n" >> "$OUT/plural-counters-reach.log"
  "$P" "$@" >> "$OUT/plural-counters-reach.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/plural-counters-reach.log"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it, and perturb.sh says of itself that it does not decide whether a red is the RIGHT red.
echo "################ 0-control" >> "$OUT/plural-counters-reach.log"
./tools/sbt -batch "$BOTH" >> "$OUT/plural-counters-reach.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/plural-counters-reach.log"

# 1. The digits on the ledger's evidence for a screened pair, which is the OTHER way into that
# file and a different line from the reading's two counts: `record(outcome)` rather than
# `record(statement, reading)`.
# Expect red on: LedgerSpec, "The digits on the evidence of a separated pair"
run "1-ledger-digits" "$LEDGER" \
  '${Prose.count(separated.agreement, "digit")}' \
  '${separated.agreement} digits' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.LedgerSpec'

# 2. The same count on the next step a separated pair produces, which is a different file and a
# different sentence about the same number.
# Expect red on: RemedySpec, "The two digit counts of this file"
run "2-remedy-separated" "$REMEDY" \
  '${Prose.count(agreement, "digit")}' \
  '$agreement digits' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'

# 3. The site the card's own census did not carry, fired on its own so that the finding is
# reproducible rather than a sentence: with 2 repaired and this one back, the same test goes red
# for the other half of its assertion.
# Expect red on: RemedySpec, "The two digit counts of this file"
run "3-remedy-not-credible" "$REMEDY" \
  '${Prose.count(confirmed, "digit")}' \
  '$confirmed digits' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'


# 4. The arity refusal of the second reader of a proof, which said `1 premises for abs` for every
#    one of the four rules whose arity is one.
# Expect red on: ParseSpec, "The refusal about a step's premises"
run "4-checker-premises" "$PARSE" \
  '${Plural.count(Step.arity(step), "premise", "premises")} for' \
  '${Step.arity(step)} premises for' \
  -- ./tools/sbt -batch 'checker/testOnly garden.xeno.symbolum.checker.ParseSpec'

# 5. The two counts of the ragged-matrix refusal, put back together because they are one sentence.
#    This is also the site whose noun is why the copies take both forms: `entry`/`entries`.
# Expect red on: PerronSpec, "The refusal about a ragged matrix"
run "5-core-entries-and-rows" "$PERRON" \
  's"row $ragged has ${Plural.count(matrix(ragged).length, "entry", "entries")} in a matrix of " +
                s"${Plural.count(size, "row", "rows")}, and an " +' \
  's"row $ragged has ${matrix(ragged).length} entries in a matrix of $size rows, and an " +' \
  -- ./tools/sbt -batch 'core/testOnly garden.xeno.symbolum.PerronSpec'

# 6. THE TRUSTED BASE, and the one site repaired by rewriting the sentence rather than by counting.
#    Putting the old sentence back is putting the count in front of the noun again.
# Expect red on: TermSpec, "The type walk's invariant violation"
run "6-kernel-binders" "$TERM" \
  's"index $index, binders in scope: ${context.length}"' \
  's"index $index with ${context.length} binders"' \
  -- ./tools/sbt -batch 'kernel/testOnly garden.xeno.symbolum.kernel.TermSpec'

# 7. The first of the three complaints a figure produces. The other two are NOT of this class:
#    both sit behind a `!= 1` guard, so neither ever prints one.
# Expect red on: MarkSpec, "The complaint about the stream"
run "7-mark-cells" "$MARK" \
  '${Plural.count(faults.length, "cell", "cells")}, " +
          s"first ${faults.head}"' \
  '${faults.length} cells, first ${faults.head}"' \
  -- ./tools/sbt -batch 'mark/testOnly garden.xeno.symbolum.mark.MarkSpec'

# 8. The refutation checker's index refusal, in the module that depends on nothing so that a search
#    which cannot see `kernel` cannot construct a theorem whatever it does.
# Expect red on: SolverSpec, "The refusal about the empty clause's index"
run "8-sat-steps" "$RESOLUTION" \
  '${Plural.count(steps.length, "step", "steps")}' \
  '${steps.length} steps' \
  -- ./tools/sbt -batch 'sat/testOnly garden.xeno.symbolum.sat.SolverSpec'


# 9. The five sites of one file that the card's list did not carry and the re-run of its census
#    found. They are one condition in one file, so one perturbation covers them: `Remedy` reaches
#    `Prose.count` and the repair there needed no decision.
# Expect red on: RemedySpec, "The point and argument counts of this file"
run "9-remedy-points" "$REMEDY" \
  '${Prose.count(asked, "point")}' \
  '$asked points' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'

# 10. The two counts of one sentence in `core`, which is the module whose second site turned the
#     private method of increment two into a file: `Plural` is shared by `Perron` and `Relation`.
# Expect red on: RelationSpec, "The refusal about precision"
run "10-core-digits-and-places" "$RELATION" \
  '${Plural.count(digits, "digit", "digits")} leaves ' \
  '$digits digits leaves ' \
  -- ./tools/sbt -batch 'core/testOnly garden.xeno.symbolum.RelationSpec'

# 11. The solver's bound, and the site with the strongest evidence of the whole card: the spec
#     asserted `within 1 conflicts` until 2026-09-20, so the defect was not merely present, it was
#     pinned by a test that passed a limit of one and copied the message back.
# Expect red on: SolverSpec, "The undecided answer"
run "11-sat-conflicts" "$SOLVER" \
  '${Plural.count(conflictLimit, "conflict", "conflicts")}' \
  '$conflictLimit conflicts' \
  -- ./tools/sbt -batch 'sat/testOnly garden.xeno.symbolum.sat.SolverSpec'


# 12. The two counts of one sentence in `logic`, which is the fifth module to need a copy and the
#     one the card's list did not reach at all: `logic` is BELOW `theories`, so the direction that
#     makes the chain a chain is what puts the shared counter out of reach.
# Expect red on: LogicErrorSpec, "The refusal about a partial instance"
run "12-logic-quantifiers" "$LOGICERROR" \
  '${Plural.count(quantifiers, "leading quantifier", "leading quantifiers")} ' \
  '$quantifiers leading quantifiers ' \
  -- ./tools/sbt -batch 'logic/testOnly garden.xeno.symbolum.logic.LogicErrorSpec'

# 13. The search bound in `theories`, which reaches one for a reason in its own arithmetic: the
#     bound is `right / answer + 1` and is literally `BigInt(1)` when the answer is zero. It is
#     also why `Prose.count` gained a `BigInt` overload rather than the call gaining a `toInt`.
# Expect red on: ValueSpec, "The refusal about a combination"
run "13-theories-steps" "$VALUE" \
  '${Prose.count(bound, "step")}' \
  '$bound steps' \
  -- ./tools/sbt -batch 'theories/testOnly garden.xeno.symbolum.theories.ValueSpec'


# 14. THE TRUSTED BASE AGAIN, and the second site in it of the shape `Term.typeIn` was repaired
#     for. `Theory.declareTypeOperator` takes any arity and `TheorySpec` declares `list` at one,
#     so `takes 1 arguments` is what every unary operator's refusal read. Repaired the kernel's
#     way, by moving the count behind its noun rather than by counting.
# Expect red on: TheorySpec, "name the arity without a noun that has to agree with it"
run "14-kernel-arity" "$KERNELERROR" \
  's"type operator $name, arity $expected, arguments given: $found"' \
  's"type operator $name takes $expected arguments, found $found"' \
  -- ./tools/sbt -batch 'kernel/testOnly garden.xeno.symbolum.kernel.TheorySpec'

# 15. The ceiling refusal in `logic`, whose two numbers are repaired two different ways inside one
#     sentence: `reached` by the counter, `allowed` by moving behind its noun. This one puts the
#     noun back and fires the first half.
# Expect red on: LogicErrorSpec, "The refusal about a term that grew"
run "15-logic-nodes" "$LOGICERROR" \
  '${Plural.count(reached, "node", "nodes")} where the ceiling in nodes is $allowed' \
  '$reached nodes where $allowed are allowed' \
  -- ./tools/sbt -batch 'logic/testOnly garden.xeno.symbolum.logic.LogicErrorSpec'

# 16. THE VERB, and the one defect here that increment three left behind a green suite. The
#     counter had already repaired the noun of this sentence; `1 argument were given` is what it
#     still said at one, and this file's own spec asserted that string. A perturbation is the only
#     instrument that can show the difference, because the assertion and the defect were copies.
# Expect red on: LogicErrorSpec, "The refusal about a partial instance"
run "16-logic-verb" "$LOGICERROR" \
  's"and was given ${Plural.count(arguments, "argument", "arguments")}: " +' \
  's"and ${Plural.count(arguments, "argument", "arguments")} were given: " +' \
  -- ./tools/sbt -batch 'logic/testOnly garden.xeno.symbolum.logic.LogicErrorSpec'

# 17. The same refusal one module up, which `Remedy` writes in its own words and which reaches
#     `Prose.count` rather than a copy. Two messages about one refusal is the arrangement, so the
#     guard is two guards and this fires the second.
# Expect red on: RemedySpec, "The ceiling counts of this file"
run "17-remedy-nodes" "$REMEDY" \
  '${Prose.count(reached, "node")} in one pass " +
          s"where the ceiling in nodes is $allowed' \
  '$reached nodes in one pass where $allowed are allowed' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'


# 18 TO 20 ARE NOT OF THE CENSUS'S CLASS, and they are here because they are the same decision.
# `argument(s)` and `thing(s)` read at every number, so none of the three was ever WRONG and no
# grep on a bare plural finds them. What they are is a second name for the counter, in two files
# that call it thirteen times between them, which is the arrangement this card spent three
# increments removing. They went the day the refusals beside them were repaired.

# 18. `Remedy`'s reading of the kernel's arity refusal, whose own sentence is perturbation 14.
# Expect red on: RemedySpec, "The two counts this file wrote with a parenthesis"
run "18-remedy-arity-parenthesis" "$REMEDY" \
  '${Prose.count(expected, "argument")}")' \
  '$expected argument(s)")' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'

# 19. The irregular noun, and the one site that needed `Prose.count` to grow rather than to be
#     called: the one-argument body appends an `s` and would say `hypothesiss`.
# Expect red on: RemedySpec, "The two counts this file wrote with a parenthesis"
run "19-remedy-hypotheses" "$REMEDY" \
  'Prose.count(hypotheses.length, "hypothesis", "hypotheses")' \
  's"${hypotheses.length} thing(s)"' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'

# 20. The third, in `theories`, and the one reached at one BY CONSTRUCTION: the branch that reads
#     a numeral passes `route.copy(arity = 1)`, so the literal one is in the source above it.
# Expect red on: ValueSpec, "The refusal about a constant's arity"
run "20-value-arity-parenthesis" "$VALUE" \
  '${Prose.count(route.arity, "argument")} and was given' \
  '${route.arity} argument(s) and was given' \
  -- ./tools/sbt -batch 'theories/testOnly garden.xeno.symbolum.theories.ValueSpec'

echo "### all twenty fired" >> "$OUT/plural-counters-reach.log"
git status --porcelain >> "$OUT/plural-counters-reach.log"
