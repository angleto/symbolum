#!/bin/sh
# Fire the partial-report case of card 32c9a285 at the defect it was written for.
#
# The verification of 2026-09-20 found `tools/coverage-delta.sh` reading the reports it happened to
# find with no notion of how many to expect: after a narrow run it printed 9 of 9 statements at
# 100.00% for a change of 176 lines across eight modules, which is a rate over one module reported
# as the rate of the change. The repair refuses when a module carrying a changed line has no report
# of this build, and `tools/coverage-delta-test.sh` case 10 is the guard.
#
# Two perturbations, because the guard has two halves and each can pass while the other is broken:
# the refusal itself, and the criterion that makes it a statement about the CHANGE rather than
# about the build. Disabling the first must make the shortfall case green; widening the second to
# every module of the build must make the control case red.
#
# The control is the run before them, in the same tree, and it must be green.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SUBJECT=tools/coverage-delta.sh
TEST='sh tools/coverage-delta-test.sh'

echo "################ 0-control" >> "$OUT/coverage-delta.log"
$TEST >> "$OUT/coverage-delta.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/coverage-delta.log"

# 1. The check removed, which is the subject as it stood when the verification ran. Expect red on:
# "a module with changed lines and no report is named" and the two checks under it.
echo "################ 1-no-check-at-all" >> "$OUT/coverage-delta.log"
"$P" "$SUBJECT" \
  'if [ -s "$work/unreported" ]; then' \
  'if false; then' \
  -- $TEST >> "$OUT/coverage-delta.log" 2>&1
echo "### exit $? for 1-no-check-at-all" >> "$OUT/coverage-delta.log"

# 2. The criterion widened from the change to the build, which is the neighbouring gate's question
# and is the wrong one here: it refuses a measurement after a narrow run of the one module a change
# touches, which is a legitimate local use. Expect red on the control case, "a module that did not
# report and did not change is not a shortfall".
echo "################ 2-criterion-is-the-build" >> "$OUT/coverage-delta.log"
"$P" "$SUBJECT" \
  'cut -f1 "$work/added" | awk -F/ '"'"'{ print $2 }'"'"' | sort -u > "$work/touched"' \
  'ls -d modules/*/src/main 2>/dev/null | awk -F/ '"'"'{ print $2 }'"'"' | sort -u > "$work/touched"' \
  -- $TEST >> "$OUT/coverage-delta.log" 2>&1
echo "### exit $? for 2-criterion-is-the-build" >> "$OUT/coverage-delta.log"

cd "$WT" && git status --porcelain >> "$OUT/coverage-delta.log"
