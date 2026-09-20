#!/bin/sh
# Fire the two both-directions guards of card db67b658 at the defect they were written for.
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

echo "### all three fired" >> "$OUT/plural-counters-reach.log"
git status --porcelain >> "$OUT/plural-counters-reach.log"
