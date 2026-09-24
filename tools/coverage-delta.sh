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
# coordinates. There is no baseline report, so there is nothing to shift. The current file is the
# one in the WORKING TREE, because that is what the report was built from: the diff is taken from
# where the change left the line to the working tree, and a source nobody has added to git yet is
# the change too. Until 2026-09-24 it was taken to `HEAD`, and an uncommitted edit above a changed
# line put every added line on a different number from the report's.
#
# WHAT IT IS NOT. It is not a replacement for the floors and does not lower one. A module can
# drift down slowly with every change well covered, which is exactly what a floor on the average
# prevents, so the two answer different questions and `docs/adr/0035` is where that is decided.
#
# Usage:
#   tools/coverage-delta.sh [BASE]          # BASE defaults to HEAD~1
#   tools/coverage-delta.sh --event NAME BEFORE PR_BASE
#
# The second form is the one `.github/workflows/ci.yml` calls, and it exists so that which base a
# runner measures from is decided here, where a test can reach it, rather than in an expression in
# YAML that only a runner evaluates: a push measures from the commit before it, a pull request from
# its base, and any other event names no change and says so.
#
# It reads the reports already on disk and runs no build: `tools/coverage-gate.sh` is what
# produces them. A report is refused when it is not one a build wrote, when it or the instrumented
# compile it was written from is older than a changed file of its module, and when a changed file
# appears in no report at all; the three are checked below, each one was a pass until 2026-09-24,
# and the compile's date was not read until 2026-09-25.
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
if [ "${1:-}" = "--event" ]; then
    [ "$#" -eq 4 ] || {
        echo "coverage-delta: --event takes three arguments: NAME BEFORE PR_BASE" >&2
        exit 2
    }
    case "$2" in
        push) base=$3 ;;
        # NOT `before`, which a pull request's synchronize event carries too: that is the previous
        # push to the branch, so the figure would be the coverage of the last push and not of the
        # change under review. The expression this replaced tried `before` first.
        pull_request) base=$4 ;;
        *)
            # A manual run, or any trigger that names no change. The expression this replaced
            # resolved to an empty string here and the step went red on every manual run.
            echo "coverage-delta: a $2 run names no change, so there is nothing to measure."
            exit 0
            ;;
    esac
elif [ "$#" -ge 1 ]; then
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
# exactly the lines that changed and not three of context either side; from the merge base so a
# branch is compared against where it left the line rather than against the line's tip, which is
# the question a reader of a change asks. A deleted file has no lines to cover, and a deleted line
# has nowhere to be covered, so only the new side is read.
#
# TO THE WORKING TREE AND NOT TO `HEAD`, decided on 2026-09-24 and recorded in `docs/adr/0035`.
# The report is built from the working tree, so its line numbers are the working tree's; a diff to
# `HEAD` is in the coordinates of a file that is not on disk whenever anything is uncommitted, and
# measured on a real report of `scan` that answered "none of those lines carries a statement" for
# a change of six statements, two of them never run. Refusing a dirty tree was the alternative and
# is correct too; it was not taken because measuring an uncommitted change is the local use this
# tool is for, and the comment here said it could.
fork=$(git merge-base "$base" HEAD 2>/dev/null) || {
    echo "coverage-delta: $base and HEAD share no history, so there is no change between them" >&2
    exit 2
}
git diff --unified=0 --diff-filter=d "$fork" -- 'modules/*/src/main/*.scala' \
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
' "$work/diff" > "$work/added.unsorted"

# A source git does not know yet is added whole: every line of it is new.
git ls-files --others --exclude-standard -- 'modules/*/src/main/*.scala' | while IFS= read -r file; do
    awk -v f="$file" '{ print f "\t" NR }' "$file"
done >> "$work/added.unsorted"
sort -u "$work/added.unsorted" > "$work/added"

added=$(grep -c . < "$work/added" || :)

if [ "$added" -eq 0 ]; then
    echo "coverage-delta: $base... adds or changes no line under modules/*/src/main; nothing to measure."
    exit 0
fi

# THE REPORTS, and whether each is one a build wrote after the change. Until 2026-09-24 their age
# was printed rather than checked, on the argument that "older than the tree" is a judgement about
# what the reader is doing. It is not, once the diff is to the working tree: a report older than a
# changed file of its module was built without that change, whatever the reader meant, and the
# shared checkout held a `<statements/>` of fourteen bytes dated 2020 in all eleven modules, which
# this passed for a change of 199 lines.
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

# NOT A REPORT A BUILD WROTE. scoverage stamps every report it writes with `timestamp`, in
# milliseconds; a file without one is not its output, whatever it is named.
for report in $reports; do
    grep -q 'timestamp="[0-9][0-9]*"' "$report" || echo "$report"
done > "$work/unstamped"
if [ -s "$work/unstamped" ]; then
    echo "coverage-delta: these carry no timestamp, so no build of scoverage wrote them:" >&2
    sed 's/^/  /' "$work/unstamped" >&2
    echo "coverage-delta: run tools/coverage-gate.sh, which writes every module's report, and ask again." >&2
    exit 2
fi

# OLDER THAN THE CHANGE, which is two dates and not one, because a report is written from what an
# instrumented compile left behind and the two are separate steps. A changed file modified after
# its module's report was written is a change that report never saw. But a report written AFTER
# the edit can still be of the tree before it: `coverageReport` alone recompiles nothing and
# rewrites `scoverage.xml` from the `scoverage-data/scoverage.coverage` of the last instrumented
# compile, and `tools/coverage-gate.sh` recommends exactly that command when its sequence stops.
# Checked against the report only, until 2026-09-25, and measured by the verification of card
# 61cdee9d on a real report of `scan`: an uncommitted line above the change, then that command,
# and this answered "none of those lines carries a statement", exit 0, on six statements of which
# two were never run. So the instrumentation's own date is compared as well, and a module whose
# report has no instrumentation beside it is refused, since nothing then says what it was built
# from.
#
# The file's modification time and not its commit's, because the report is of the working tree;
# a checkout rewrites the times of what it changes, so a report built on another branch reads as
# older than every file that branch differs in.
cut -f1 "$work/added" | sort -u | while IFS= read -r file; do
    module=$(printf '%s\n' "$file" | awk -F/ '{ print $2 }')
    for report in modules/"$module"/target/scala-*/scoverage-report/scoverage.xml; do
        data=${report%/scoverage-report/scoverage.xml}/scoverage-data/scoverage.coverage
        if [ ! -f "$data" ]; then
            printf 'NODATA\t%s\n' "$data"
        elif [ -n "$(find "$file" -newer "$data" 2>/dev/null)" ]; then
            printf 'COMPILE\t%s\n' "$file"
        elif [ -n "$(find "$file" -newer "$report" 2>/dev/null)" ]; then
            printf 'REPORT\t%s\n' "$file"
        fi
    done
done | sort -u > "$work/newer"
if grep -q '^NODATA' "$work/newer"; then
    echo "coverage-delta: these reports have no instrumentation beside them, so nothing says which" >&2
    echo "coverage-delta: tree they were written from:" >&2
    grep '^NODATA' "$work/newer" | cut -f2 | sed 's/^/  /' >&2
    echo "coverage-delta: run tools/coverage-gate.sh, which writes both, and ask again." >&2
    exit 2
fi
if grep -q '^COMPILE' "$work/newer"; then
    echo "coverage-delta: these changed after the instrumented compile their module's report was" >&2
    echo "coverage-delta: written from, so the report is of a tree without them, however recent it is:" >&2
    grep '^COMPILE' "$work/newer" | cut -f2 | sed 's/^/  /' >&2
    echo "coverage-delta: \`coverageReport\` alone does not recompile; run tools/coverage-gate.sh and ask again." >&2
    exit 2
fi
if [ -s "$work/newer" ]; then
    echo "coverage-delta: these changed after their module's report was written, so the report" >&2
    echo "coverage-delta: is of a tree without them:" >&2
    cut -f2 "$work/newer" | sed 's/^/  /' >&2
    echo "coverage-delta: build the report again (tools/coverage-gate.sh) and ask again." >&2
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
        if (hit != "") seen[hit] = 1
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
        for (f in files) if (!(f in seen)) print "UNSEEN " f
    }
' "$work/added" $reports > "$work/counted"

# A CHANGED FILE NO REPORT MENTIONS, which left the denominator in silence until 2026-09-24: a
# fixture of 42 changed lines of code read "20 of 20 = 100.00%" because the file holding 22 of
# them was in no report. That is the module check above one level down, and it refuses for the
# same reason. The cost is a file with no statement at all, which a report cannot list either:
# measured on 2026-09-24, none of the 183 sources under modules/*/src/main is free of `def`, `val`
# and `var`, so no file of this repository is expected to meet it.
grep '^UNSEEN ' "$work/counted" | sed 's/^UNSEEN //' | sort > "$work/unseen"
if [ -s "$work/unseen" ]; then
    echo "coverage-delta: these carry changed lines and appear in no report, so none of their" >&2
    echo "coverage-delta: statements is in the figure:" >&2
    sed 's/^/  /' "$work/unseen" >&2
    echo "coverage-delta: a report built incrementally lists only what it recompiled; run" >&2
    echo "coverage-delta: tools/coverage-gate.sh, which cleans first, and ask again." >&2
    exit 2
fi

total=$(head -1 "$work/counted" | cut -d' ' -f1)
covered=$(head -1 "$work/counted" | cut -d' ' -f2)

# The newest report's own stamp, read as a number. This sorted the `ls -l` date columns as text
# until 2026-09-24, so reports of the 3rd and the 22nd of a month printed the 3rd, and of the 30th
# of September and the 1st of October printed the 30th.
stamp=$(cat $reports | sed -n 's/.*timestamp="\([0-9][0-9]*\)".*/\1/p' | sort -n | tail -1)
seconds=$((stamp / 1000))
newest=$(date -u -d "@$seconds" '+%Y-%m-%d %H:%M UTC' 2>/dev/null \
    || date -u -r "$seconds" '+%Y-%m-%d %H:%M UTC')

echo "coverage-delta: $base... to the working tree"
echo "coverage-delta: $added line(s) added or changed under modules/*/src/main"
# The positive half of the check above, printed on every run rather than only when it bites: a
# reader who is told what was missing on the bad path and nothing at all on the good one has to
# take the good one on trust.
echo "coverage-delta: every one of the $(grep -c . < "$work/touched") module(s) it touches has a report, written from an"
echo "coverage-delta: instrumented compile, and both are newer than every changed file of that module"
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
