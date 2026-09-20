#!/bin/sh
# Fire the eleven both-directions guards of card db67b658 at the defect they were written for.
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
# The strings are literal and were unique at 372a025. perturb.sh REFUSES a perturbation that did
# not apply rather than running against unperturbed code, so a refusal means the source moved.
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

echo "### all thirteen fired" >> "$OUT/plural-counters-reach.log"
git status --porcelain >> "$OUT/plural-counters-reach.log"
