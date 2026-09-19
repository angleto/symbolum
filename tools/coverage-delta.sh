#!/bin/sh
# What the lines a change ADDED are covered at, which is a figure the module average is not.
#
# WHY THIS EXISTS. The floors in `build.sbt` are on a module's average, and an average is not a
# property of the module: it is a property of the pair (module, set of suites that ran). Measured
# on 2026-09-18 at `30a1452`, same tree, same code, two commands minutes apart:
#
#     clean coverage theories/test theories/coverageReport   54027/55521 = 97.309%   FAILS
#     clean coverage test coverageReport                     54113/55521 = 97.464%   passes
#
# **86 statements of difference on one tree**, because scoverage attributes every execution of an
# instrumented class to the module that owns the source, and `tactics`, `checker` and `dist`
# execute `theories`. The slack the floors leave is about 25 statements; the number one tree moves
# by changing the command is three times that.
#
# The coverage of what a change adds does not move that way. A new statement is executed by
# somebody or it is not, and who else runs the file does not enter it. So this figure is the same
# under both commands, which is the defect card 32c9a285 exists to close.
#
# HOW IT AVOIDS THE PROBLEM EVERY COVERAGE-DIFF TOOL HAS. The obvious construction is to compare
# two `scoverage.xml` files, and it is wrong: one line inserted in a file moves the line number of
# every statement below it, so the naive comparison reports the whole rest of the file as new.
# **Nothing here compares two reports.** It reads the added lines out of `git diff` in the
# coordinates of the CURRENT file, and reads the current report, which is in those same
# coordinates. There is no baseline report, so there is nothing to shift.
#
# WHAT IT IS NOT. It is not a replacement for the floors and does not lower one. A module can
# drift down slowly with every change well covered, which is exactly what a floor on the average
# prevents, so the two answer different questions and `docs/adr/0035` is where that is decided.
#
# Usage:
#   tools/coverage-delta.sh [BASE]          # BASE defaults to HEAD~1
#
# It reads the reports already on disk and runs no build: `tools/coverage-gate.sh` is what
# produces them, and a report older than the working tree is the one failure mode this cannot
# see, which is why it prints the report's own timestamp beside the figure.
#
# Exit codes: 0 when the rate is at or above the threshold or nothing was added, 1 when it is
# below, 2 when it could not measure -- which is never reported as a pass, for the reason
# `tools/coverage-gate.sh` exists.

set -u

# The repository this is asked about is the one the caller is standing in, not the one the script
# happens to live in. Two reasons and the second is the one that mattered: a tool run from a
# subdirectory should answer about the checkout, and the test beside this one runs the subject
# against repositories built for the purpose, which a path derived from `$0` could never reach.
root=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "coverage-delta: not inside a git repository" >&2
    exit 2
}
cd "$root" || exit 2

base=${1:-HEAD~1}

# The threshold, and it is deliberately not a floor in `build.sbt`. See `docs/adr/0035` for the
# measurement that chose it; it is an environment variable so a session can ask "what would this
# have said at 95" without editing a tracked file.
minimum=${COVERAGE_DELTA_MIN:-90}

# BELOW THIS MANY STATEMENTS THE FIGURE IS REPORTED AND NOT JUDGED, and the number follows from
# the threshold rather than being a second taste. A change of n statements with one uncovered
# reads (n-1)/n, so at the floor above it takes ten before a single miss is survivable: at five
# statements one miss is 80% and fails, which would make the gate a rule about the size of a
# change. Raise the floor and this rises with it, which is why it is computed and not written.
#
#   minimum 90  ->  10 statements       minimum 95  ->  20        minimum 80  ->  5
coarse=$(awk -v m="$minimum" 'BEGIN { printf "%d", (m >= 100 ? 0 : 100 / (100 - m) + 0.999) }')

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT INT TERM

if ! git rev-parse --verify --quiet "$base" >/dev/null; then
    echo "coverage-delta: no such revision: $base" >&2
    exit 2
fi

# THE ADDED LINES, in the coordinates of the working tree. `--unified=0` so a hunk header names
# exactly the lines that changed and not three of context either side; `...` so a branch is
# compared against where it left the line rather than against the line's tip, which is the
# question a reader of a change asks. A deleted file has no lines to cover, and a deleted line
# has nowhere to be covered, so only the new side is read.
git diff --unified=0 --diff-filter=d "$base"...HEAD -- 'modules/*/src/main/*.scala' \
    > "$work/diff" 2>"$work/diff.err" || {
        echo "coverage-delta: git diff against $base failed" >&2
        cat "$work/diff.err" >&2
        exit 2
    }

awk '
    /^\+\+\+ b\// { file = substr($0, 7); next }
    /^@@ / {
        # @@ -old,n +new,m @@ ; m defaults to 1 when absent, and m = 0 is a pure deletion.
        split($3, plus, ",")
        start = plus[1]; sub(/^\+/, "", start)
        count = (plus[2] == "" ? 1 : plus[2])
        for (i = 0; i < count; i++) print file "\t" (start + i)
    }
' "$work/diff" | sort -u > "$work/added"

added=$(grep -c . < "$work/added" || :)

if [ "$added" -eq 0 ]; then
    echo "coverage-delta: $base...HEAD adds or changes no line under modules/*/src/main; nothing to measure."
    exit 0
fi

# THE REPORTS. Their age is printed rather than checked, because "older than the tree" is a
# judgement about what the reader is doing and a wrong guess either way is worse than the date:
# a session measuring an uncommitted change wants the report it just built, and one measuring a
# commit wants the report of that commit.
reports=$(find modules/*/target/scala-*/scoverage-report/scoverage.xml 2>/dev/null | sort)
if [ -z "$reports" ]; then
    echo "coverage-delta: no coverage report on disk. Run tools/coverage-gate.sh first." >&2
    exit 2
fi

# The statements of this run that sit on an added line. A statement is the unit the floors count
# in, so it is the unit here: a line carrying three statements weighs three, which is what keeps
# this figure comparable with the ones in `build.sbt`.
#
# MATCHED BY SUFFIX AND NOT BY STRIPPING A PREFIX, which is the one thing in this file that was
# got wrong first. `source=` is absolute and the diff is relative, so the obvious move is to
# remove the repository root from the front of the first -- and on macOS the root the report was
# written under is `/Users/...` while `git rev-parse --show-toplevel` in a temporary directory
# answers `/private/var/...` for the same place. Every statement then failed to match and the
# subject reported, correctly by its own lights, that no changed line carried one. A suffix
# comparison does not care which name the same directory was reached by.
# shellcheck disable=SC2086
awk '
    FILENAME == ARGV[1] {
        wanted[$1 "\t" $2] = 1
        files[$1] = 1
        next
    }
    /source="/ {
        match($0, /source="[^"]*"/)
        src = substr($0, RSTART + 8, RLENGTH - 9)
        match($0, /line="[0-9]*"/)
        ln = substr($0, RSTART + 6, RLENGTH - 7)
        hit = ""
        for (f in files) {
            n = length(f)
            if (substr(src, length(src) - n) == "/" f || src == f) { hit = f; break }
        }
        if (hit == "" || !((hit "\t" ln) in wanted)) next
        match($0, /invocation-count="[0-9]*"/)
        hits = substr($0, RSTART + 18, RLENGTH - 19) + 0
        total++
        if (hits > 0) covered++
        else uncovered[hit "\t" ln] = 1
    }
    END {
        printf "%d %d\n", total, covered
        for (k in uncovered) print "MISS " k
    }
' "$work/added" $reports > "$work/counted"

total=$(head -1 "$work/counted" | cut -d' ' -f1)
covered=$(head -1 "$work/counted" | cut -d' ' -f2)

newest=$(find modules/*/target/scala-*/scoverage-report/scoverage.xml -exec ls -l {} + 2>/dev/null \
    | awk '{print $6, $7, $8}' | sort | tail -1)

echo "coverage-delta: $base...HEAD"
echo "coverage-delta: $added line(s) added or changed under modules/*/src/main"
echo "coverage-delta: reports last written around $newest"

if [ "$total" -eq 0 ]; then
    # NOT A PASS BY DEFAULT, and this is the branch where an instrument that did not read looks
    # most like a clean result. Changed lines with no statement on them are ordinary -- a comment,
    # a signature, a blank -- but so is a report that predates the change, and the two are not
    # distinguishable from here. The verdict says which of the two a reader has to rule out.
    echo "coverage-delta: none of those lines carries a statement in any report of this build."
    echo "coverage-delta: That is the ordinary answer for comments, blank lines and signatures,"
    echo "coverage-delta: AND it is what a stale report gives for a change full of new code."
    echo "coverage-delta: Check the date above against the change before reading it as a pass."
    exit 0
fi

rate=$(awk -v c="$covered" -v t="$total" 'BEGIN { printf "%.2f", 100 * c / t }')
echo "coverage-delta: $covered of $total statement(s) on those lines were executed = $rate% (floor $minimum%)"

if [ "$total" -lt "$coarse" ]; then
    echo "coverage-delta: fewer than $coarse statements, so the rate is reported and not judged:"
    echo "coverage-delta: one miss out of $total is $(awk -v t="$total" 'BEGIN { printf "%.0f", 100 * (t - 1) / t }')%, which the floor"
    echo "coverage-delta: would fail, and a gate that fails on the size of a change is not this one."
    grep '^MISS ' "$work/counted" | sed 's/^MISS /  not executed: /' | sort
    exit 0
fi

if awk -v r="$rate" -v m="$minimum" 'BEGIN { exit !(r + 0 < m + 0) }'; then
    echo "coverage-delta: BELOW the floor. The statements nobody executed:"
    grep '^MISS ' "$work/counted" | sed 's/^MISS /  /' | sort | head -40
    exit 1
fi

echo "coverage-delta: at or above the floor."
exit 0
