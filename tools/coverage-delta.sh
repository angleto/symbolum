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
# The coverage of what a change adds barely moves that way, and "barely" is measured rather than
# hoped. Over one window on 2026-09-19, base `7cb7d148`, restricted to `theories`: the wide
# command reads 3111 of 3164 and the narrow one 3109 of 3164, the same denominator and two
# statements apart, 98.32% against 98.26%. The module average over the same pair reads 97.52%
# and 97.32%, and **crosses its floor**.
#
# The two statements are on one line, `Linarith.scala:1743`, which only a suite outside
# `theories` calls: the mechanism is the same one, with a lever short enough that no difference
# of that origin can decide a floor of 90. `docs/adr/0035` carries the table.
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
# `tools/coverage-gate.sh` exists. A module carrying a changed line and no report of this build
# is one of those 2s, and not a rate over the modules that did report: see the check below.

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

# `${1:-HEAD~1}` was wrong here and the difference only shows on a runner: it treats an EMPTY
# argument as an absent one, and the caller in `.github/workflows/ci.yml` passes an expression
# that can resolve to nothing. Falling back to `HEAD~1` there would compare a merge against one
# of its parents and call the answer the change, which is a figure nobody asked for reported as
# though they had. An absent argument is a person at a shell; an empty one is a CI expression
# that produced nothing, and they get different answers.
if [ "$#" -ge 1 ]; then
    base=$1
else
    base=HEAD~1
fi

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

# THE FIRST PUSH ON A REF HAS NO BASE, and GitHub says so by sending forty zeros as
# `github.event.before`. There is nothing to compare against and that is not a misconfiguration,
# so it is a line and a green exit rather than a refusal. An unresolvable base that is NOT that
# is the shallow-clone case and stays a refusal, because it is a fact about the checkout.
case "$base" in
    0000000000000000000000000000000000000000)
        echo "coverage-delta: no base revision (the first push on this ref), so there is no"
        echo "coverage-delta: change to measure the coverage of."
        exit 0
        ;;
    "")
        echo "coverage-delta: the base was passed as an empty string, which is a caller whose" >&2
        echo "coverage-delta: expression resolved to nothing. Naming no base and naming an empty" >&2
        echo "coverage-delta: one are different mistakes and neither is a figure." >&2
        exit 2
        ;;
esac

# `^{commit}` and not the bare name, which is the difference between asking whether the string
# LOOKS like an object and whether the object is here. A full forty-character hex passes
# `rev-parse --verify` on its syntax alone, so a missing base from a shallow clone -- which is
# exactly forty characters -- got past this and failed two screens later as "git diff failed",
# with a message about the wrong thing. Found by the case in `tools/coverage-delta-test.sh`
# refusing for the right exit code and the wrong reason.
if ! git rev-parse --verify --quiet "$base^{commit}" >/dev/null 2>&1; then
    echo "coverage-delta: no such revision: $base. On a runner this is a shallow clone: the" >&2
    echo "coverage-delta: coverage job needs fetch-depth: 0 to have a base to diff against." >&2
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

# AND ENOUGH OF THEM, which is a different question from whether there are any. This read the
# reports it found and had no notion of how many to expect, so after a narrow run it printed a
# rate for the whole change computed over the one module that reported: 9 of 9 statements at
# 100.00% on a change of 176 lines across eight modules, with nothing in the output naming the
# second element. That is the defect this whole tool is about -- a figure that is a property of
# the pair (subject, set of reports that happen to exist) -- appearing inside the tool written to
# remove it, and it was found by the verification of card 32c9a285 on 2026-09-20.
#
# The set to compare against is NOT every module of the build, which is what `tools/coverage-gate.sh`
# asks the disk for, and the difference is the whole of why this check is sharper than the one
# next door: the figure here is about the changed lines, so a module with no changed line hides
# nothing by not reporting, and a module with changed lines and no report makes every one of its
# statements invisible while the rate still prints.
#
# It refuses rather than qualifying, which follows the precedent this file already sets twice: an
# empty base and a missing revision are both refusals, because answering a question nobody asked
# as though they had is the failure this tool exists to prevent.
cut -f1 "$work/added" | awk -F/ '{ print $2 }' | sort -u > "$work/touched"
printf '%s\n' "$reports" | awk -F/ '{ print $2 }' | sort -u > "$work/reporting"
comm -23 "$work/touched" "$work/reporting" > "$work/unreported"

if [ -s "$work/unreported" ]; then
    echo "coverage-delta: the change touches $(grep -c . < "$work/touched") module(s) under" >&2
    echo "coverage-delta: modules/*/src/main and $(grep -c . < "$work/reporting") module(s) have a report on disk." >&2
    echo "coverage-delta: No report, so every statement of these is invisible here:" >&2
    sed 's/^/  /' "$work/unreported" >&2
    echo "coverage-delta: A rate over the rest would be the coverage of part of this change" >&2
    echo "coverage-delta: reported as the coverage of the change, which is the defect this tool" >&2
    echo "coverage-delta: exists to remove. A narrow run leaves this behind: run" >&2
    echo "coverage-delta: tools/coverage-gate.sh, or build the missing module's report, and ask again." >&2
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
# The positive half of the check above, printed on every run rather than only when it bites: a
# reader who is told what was missing on the bad path and nothing at all on the good one has to
# take the good one on trust.
echo "coverage-delta: every one of the $(grep -c . < "$work/touched") module(s) it touches has a report of this build"
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
