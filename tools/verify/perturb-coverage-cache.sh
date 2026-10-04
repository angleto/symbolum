#!/bin/sh
# Fire the repair that keeps an instrumented compilation out of sbt 2's disk cache, card 4335880b.
#
# The defect: after `clean`, sbt 2 answers an instrumented compilation from its disk cache, which
# restores the classes and not the `scoverage-data` directory beside them, so the first statement a
# test executes writes into a directory that is gone. The repair is the `Global / cacheVersion`
# setting in `build.sbt`, which draws a fresh version whenever `coverage` is set. Nothing inside a
# test run can see it, because the failure is in what the build hands the run, so this is the
# check: the same two runs with the repair and without it.
#
# Each case is `clean coverage sat/test sat/coverageReport` twice in a row on one tree. `sat`
# because it is small and its instrumented classes are what the defect breaks; the module is not
# what is being tested. Two runs because on a tree nobody has built the first compiles under any
# version; on a tree that has been built, the first may already meet an entry an earlier run left.
#
# WHAT WAS SEEN, 2026-10-04, in worktree `coverage-cache` at 7.0 `c9d4101b` plus the repair.
#   0-control (repair present): both runs green, 19 tests, `compiling 4 Scala sources` to
#     `symbolum-sat/classes` in each, 93.71% both times, which is CI's gate reading for `sat`.
#   1-the-version-left-alone: red at the FIRST run of the pair, `java.io.FileNotFoundException:
#     .../symbolum-sat/scoverage-data/scoverage.measurements...`, because earlier runs on that tree
#     had left entries under the default version. That is the defect as it was first met, in a
#     second `tools/coverage-gate.sh`. Seen before the repair existed too, on the same tree: `tools/
#     sbt -batch clean coverage sat/test` twice, green and then red with the same exception.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/coverage-cache.log"
TWICE='./tools/sbt -batch clean coverage sat/test sat/coverageReport && ./tools/sbt -batch clean coverage sat/test sat/coverageReport'

echo "################ 0-control" >> "$LOG"
sh -c "$TWICE" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The version left to sbt's default under coverage too, which is the build before the repair:
# the second run's instrumented compile is a cache hit and its data directory does not exist.
echo "################ 1-the-version-left-alone" >> "$LOG"
"$P" build.sbt \
  'if ((ThisBuild / coverageEnabled).value) System.nanoTime() else sbtDefault' \
  'sbtDefault' \
  -- sh -c "$TWICE" >> "$LOG" 2>&1
echo "### exit $? for 1-the-version-left-alone" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
