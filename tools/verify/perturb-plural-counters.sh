#!/bin/sh
# Fire the three both-directions guards of card 0da00ff8 at the defect they were written for.
#
# The defect is one shape at three sites in `modules/tactics`: a count interpolated bare in front
# of a noun that carries its plural in the literal, so a page resting on one axiom read `1 axioms`.
# The repair routes all three through `Prose.count`, so each perturbation here puts ONE site back
# to the bare interpolation and leaves the other two repaired: a helper that went singular
# everywhere is a different failure and would take all three down at once, which is what the
# assertions are shaped to tell apart.
#
# Two of the three guards were written on 2026-09-18 with the repair (`06fbd17`) and never seen
# red; the third, in `LedgerSpec`, was written on 2026-09-19 against a site that already carried
# the repair and had nothing asserting it. This file is what lets any of that be checked without
# taking the delivery's word for it.
#
# The strings are literal and were unique at 66dd288. perturb.sh REFUSES a perturbation that did
# not apply rather than running against unperturbed code, so a refusal means the source moved.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

COST=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Cost.scala
LEDGER=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Ledger.scala
ARGUMENT=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Argument.scala

run() { n="$1"; shift
  echo "################ $n" >> "$OUT/plural-counters.log"
  "$P" "$@" >> "$OUT/plural-counters.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/plural-counters.log"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it, and perturb.sh says of itself that it does not decide whether a red is the RIGHT red.
echo "################ 0-control" >> "$OUT/plural-counters.log"
./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.CostSpec garden.xeno.symbolum.tactics.LedgerSpec garden.xeno.symbolum.tactics.ArgumentSpec' \
  >> "$OUT/plural-counters.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/plural-counters.log"

# 1. The axiom count on the page `Ask` prints, which is the site that was MEASURED saying
# "77 inferences over 1 axioms" at `c10d61c`. Only the axiom half goes back, so the inference half
# stays repaired and the failure names one column rather than the line.
# Expect red on: CostSpec, "The two counts on the proof line ... singular at one"
run "1-cost-axioms" "$COST" \
  '${Prose.count(report.axioms.size, "axiom")}' \
  '${report.axioms.size} axioms' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.CostSpec'

# 2. The same count on the ledger's evidence for a reading, which is a different line in a
# different file and was the site with nothing asserting it until 2026-09-19.
# Expect red on: LedgerSpec, "The two counts on the evidence of a reading ... singular at one"
run "2-ledger-axioms" "$LEDGER" \
  '${Prose.count(reading.axioms, "axiom")}' \
  '${reading.axioms} axioms' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.LedgerSpec'

# 3. The claim count on the summary line of a document. This one is worth firing rather than
# assuming from the two above, because `Argument` is the site where two counts shared one noun and
# the repair gave each its own; a perturbation on `claim` leaves that pair alone and so separates
# the ordinary defect from the one that needed the sentence rewritten.
# Expect red on: ArgumentSpec, "The counts on the summary line ... singular at one"
run "3-argument-claims" "$ARGUMENT" \
  '${Prose.count(lines.length, "claim")}' \
  '${lines.length} claims' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.ArgumentSpec'

echo "### all three fired" >> "$OUT/plural-counters.log"
git status --porcelain >> "$OUT/plural-counters.log"
