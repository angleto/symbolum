#!/bin/sh
# Fire the rewriter's size ceiling at the defect it was written for, card 92f1568f.
#
# What is guarded is that a rule set which MULTIPLIES the term stops, and stops for a reason a
# caller can tell from the step limit running out. Three incidents reached an hour of wall clock,
# 540 s of processor and an exhausted heap, and in none of them was the step limit approached.
# `docs/adr/0037` is the decision and carries the measurement the number rests on.
#
# Each perturbation below takes away one thing the guard rests on and the two suites must go red.
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-22, on the tree that landed this. Control green at 32 tests in `logic`,
# 6 in `theories` and 36 in `tactics`; all four red; restore verified clean. Two of the four did
# not fail as assertions, and that is the result rather than a disappointment:
#
#   1. The ceiling raised sixty-four times, to 4194304 nodes. The JVM died with
#      `java.lang.OutOfMemoryError: Java heap space` before any assertion could run. The spec's
#      own guard on the relation the number was chosen by never got a turn, because the number
#      being too high is not something a test outlives. It also bounds the number from above by
#      measurement rather than by argument: 4.2 million nodes does not fit the gigabyte heap this
#      build runs at and 65536 does.
#   2. The width never read, which is the tree before 2026-09-22 with the tests of after it.
#      `OutOfMemoryError` again, from the same doubling rule with nothing but the step limit in
#      front of it. This is the incident of 2026-09-18 reproduced rather than described.
#   3. `Induct.afterRewriting` reading the third outcome as the second: red on the end-to-end
#      test, `NotNormalised(...)` where `GrewPastCeiling` is wanted, and the term it prints is
#      the doubled one, several thousand nodes of `real_add` printed into the failure. The two
#      remedies are opposites, which is the one distinction `docs/adr/0037` is about.
#   4. The remedy collapsed onto `RaiseALimit`: red in `RemedySpec`, on the assertion that reads
#      WHICH remedy rather than that there is one. A census counting the cases would pass here.

set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

REWRITE=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rewrite.scala
INDUCT=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Induct.scala
REMEDY=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Remedy.scala
SPECS='logic/testOnly garden.xeno.symbolum.logic.RewriteSpec'
INDUCTSPEC='theories/testOnly garden.xeno.symbolum.theories.InductSpec'
REMEDYSPEC='tactics/testOnly garden.xeno.symbolum.tactics.RemedySpec'
LOG="$OUT/rewriters-ceiling.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPECS" "$INDUCTSPEC" "$REMEDYSPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The number raised out of reach. A ceiling is a decision and the number can be edited without
# the argument being reread, which is why what is asserted is the RELATION it was chosen by: at
# least eight times the widest term this corpus carries and at most sixteen.
echo "################ 1-the-ceiling-raised-out-of-reach" >> "$LOG"
"$P" "$REWRITE" \
  '  val DefaultCeiling: Int = 65536' \
  '  val DefaultCeiling: Int = 65536 * 64' \
  -- ./tools/sbt -batch "$SPECS" >> "$LOG" 2>&1
echo "### exit $? for 1-the-ceiling-raised-out-of-reach" >> "$LOG"

# 2. The width never read, which is the tree before 2026-09-22 with the tests of after it. The
# doubling rule then has nothing but the step limit in front of it, and the run reproduces the
# incident rather than describing it.
echo "################ 2-the-width-never-read" >> "$LOG"
"$P" "$REWRITE" \
  '                val width = nodesOf(next)' \
  '                val width = 0' \
  -- ./tools/sbt -batch "$SPECS" "$INDUCTSPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-width-never-read" >> "$LOG"

# 3. The caller reading the third outcome as the second. The distinction is the whole decision:
# a rewriting that ran out of steps is settled by a higher limit and one that ran out of room is
# made worse by it, so collapsing them gives a reader the advice that lengthens the run.
echo "################ 3-the-ceiling-read-as-a-limit" >> "$LOG"
"$P" "$INDUCT" \
  '          case Rewrite.Stop.Size(nodes) =>
            Left(GrewPastCeiling(rewritten, nodes, Rewrite.DefaultCeiling))' \
  '          case Rewrite.Stop.Size(_) =>
            Left(NotNormalised(rewritten))' \
  -- ./tools/sbt -batch "$INDUCTSPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-ceiling-read-as-a-limit" >> "$LOG"

# 4. The remedy collapsed onto the one beside it. A census that only counted the cases would pass
# with both mapped to `RaiseALimit`, which is why the assertion is on which remedy and not on
# there being one.
echo "################ 4-the-remedy-collapsed" >> "$LOG"
"$P" "$REMEDY" \
  '    case GrewPastCeiling(term, reached, allowed) =>
      ReportADefect(' \
  '    case GrewPastCeiling(term, reached, allowed) =>
      RaiseALimit("the rewriting step limit", ' \
  -- ./tools/sbt -batch "$REMEDYSPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-remedy-collapsed" >> "$LOG"

echo "log: $LOG"
