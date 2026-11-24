#!/bin/sh
# Measure, for Mycelium card f0016ec8, that a forked test failing with a long message makes
# `test` exit non-zero, which under sbt 2.0.9 it did not, and that `ForkedVerdict` is what does it.
#
# 0. The control: `scan/test` green, and the verdict line naming one suite read.
# 1. The defect: one assertion of `CommentsSpec` turned into a throw whose message is 100 001
#    characters long. Before `ForkedVerdict` this exited 0 with `[success]` over ScalaTest's
#    `failed 1`; with it, the run should exit 1 with the verdict's refusal naming the suite.
# 2. The guard removed while the defect stays: the same throw, with `ForkedVerdict.verdict` reading
#    no failure. The run should exit 0 again, which says the refusal in 1 is the verdict's and not
#    sbt's own.
# 3. The completeness half: the report directory emptied by the verdict itself before it reads, so
#    a passing run has no report from a discovered suite. The run should refuse with "no report
#    from [garden.xeno.symbolum.scan.CommentsSpec]".
#
# Unlike the other harnesses here, this one is read by its `### exit` lines AND its log, because
# the exit code is the thing it measures.
#
# WHAT WAS SEEN, 2026-11-24, on the tree that became the commit carrying this file, all four as
# predicted and the tree restored after each:
# 0. exit 0, "the fork's own reports: 1 suites, 17 tests, 0 failed or in error".
# 1. exit 1, the reports reading "1 failed or in error" and the refusal "ScalaTest's own reports say
#    these suites did not pass, whatever sbt reported above", on `scan / Test / testFull`.
# 2. exit 0 with the reports still reading "1 failed": the verdict blinded, sbt's own result says
#    the run passed, which is the defect, and so the refusal in 1 is the verdict's.
# 3. exit 1, "no report from [garden.xeno.symbolum.scan.CommentsSpec]".
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SPEC_FILE=modules/scan/src/test/scala/garden/xeno/symbolum/scan/CommentsSpec.scala
VERDICT=project/ForkedVerdict.scala
LOG="$OUT/forked-verdict.log"
LONG='throw new IllegalStateException("x" * 100001)'

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch scan/test >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-a-long-message" >> "$LOG"
"$P" "$SPEC_FILE" 'line.code shouldBe "foo(); "' "$LONG" -- \
  ./tools/sbt -batch scan/test >> "$LOG" 2>&1
echo "### exit $? for 1-a-long-message" >> "$LOG"

echo "################ 2-the-verdict-blind" >> "$LOG"
"$P" "$VERDICT" 'val failed = read.filter(report => report.failures + report.errors > 0)' \
  'val failed = read.filter(report => false)' -- \
  "$P" "$SPEC_FILE" 'line.code shouldBe "foo(); "' "$LONG" -- \
  ./tools/sbt -batch scan/test >> "$LOG" 2>&1
echo "### exit $? for 2-the-verdict-blind" >> "$LOG"

echo "################ 3-no-report" >> "$LOG"
"$P" "$VERDICT" '    val read = reports(reportDirectory)' \
  '    IO.delete(reportDirectory); val read = reports(reportDirectory)' -- \
  ./tools/sbt -batch scan/test >> "$LOG" 2>&1
echo "### exit $? for 3-no-report" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
