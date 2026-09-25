#!/bin/sh
# Run `tools/coverage-delta.sh` against repositories built for the purpose, one per answer.
#
# WHY A BUILT REPOSITORY AND NOT THIS ONE. The subject's whole content is a relation between two
# things that both have to be controlled at once: which lines a change touched, and which of the
# statements on those lines were executed. On this checkout neither is settable, so the only
# assertion available is "it printed a number", which is what a subject that had stopped reading
# the report would also print. Here the diff is written by the fixture and the report is written
# by the fixture, so every case knows the answer before it asks.
#
# WHAT IT DOES NOT COVER, named rather than left to be found. Whether scoverage's `scoverage.xml`
# really carries the three attributes read here -- `source`, `line`, `invocation-count` -- which
# is a fact about that tool and is checked by the subject's real runs, where a wrong attribute
# name reads as "no statement on any changed line" on a change full of new code. That reading is
# the one case the subject refuses to call a pass, which is why the failure would be loud.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/coverage-delta.sh"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=coverage-delta-test
. "$here/test-harness.sh"

failures=0

# What scoverage stamps a report with, in milliseconds. Every fixture report carries one because
# the subject refuses a report without, which is what a stub nobody's build wrote looks like.
stamp=$(($(date +%s) * 1000))

# Sources dated before the reports that describe them, which is the order a build produces. A
# fixture writes both within a second, and the subject refuses a report older than a changed file.
#
# And beside every report, the instrumentation it was written from, dated with it: scoverage writes
# `scoverage-data/scoverage.coverage` at the instrumented compile and `coverageReport` reads it, so
# a real report never exists without one, and since 2026-09-25 the subject refuses a report that
# has none (case 16b) or whose compile is older than a changed file (case 16). Its content is never
# read, only its date.
age() {
    find "$1/modules" -path '*/src/*' -type f -exec touch -t 202601010000 {} +
    for report in "$1"/target/out/jvm/scala-*/symbolum-*/scoverage-report/scoverage.xml; do
        [ -f "$report" ] || continue
        data="${report%/scoverage-report/scoverage.xml}/scoverage-data"
        mkdir -p "$data"
        printf 'instrumentation\n' > "$data/scoverage.coverage"
    done
}

# A repository with one module, a first commit, and then a change of `$1` statements of which
# `$2` are recorded as executed. The report is written by hand: the subject reads the numbers it
# finds, and a fixture that ran a real build would be measuring scoverage rather than this.
build() {
    name="$1"; added="$2"; covered="$3"
    repo="$work/$name"
    src="modules/demo/src/main/scala/Demo.scala"
    mkdir -p "$repo/$(dirname "$src")" "$repo/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report"
    (
        cd "$repo"
        git_q init
        printf 'object Demo {\n}\n' > "$src"
        git_q add -A
        git_q commit -m base
    )

    # The change: `added` lines, each carrying exactly one statement, appended after line 1.
    {
        echo 'object Demo {'
        i=1
        while [ "$i" -le "$added" ]; do
            echo "  def f$i(): Int = $i"
            i=$((i + 1))
        done
        echo '}'
    } > "$repo/$src"
    (
        cd "$repo"
        git_q add -A
        git_q commit -m change
    )

    # The report, in the shape scoverage writes: one `<statement>` per line of the file, with the
    # first `covered` of them executed. Line 1 and the last line are the braces and carry none,
    # which is why the statements start at line 2.
    {
        echo '<scoverage statement-count="'"$added"'" timestamp="'"$stamp"'">'
        i=1
        while [ "$i" -le "$added" ]; do
            hits=0
            [ "$i" -le "$covered" ] && hits=1
            echo '<statement source="'"$repo/$src"'" line="'$((i + 1))'" invocation-count="'"$hits"'">'
            echo '</statement>'
            i=$((i + 1))
        done
        echo '</scoverage>'
    } > "$repo/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
    age "$repo"
}

# A repository with TWO modules, each changed and each reporting, which is what the partial-report
# case has to be built out of: with one module there is no difference between "no report" and "a
# report for every module the change touches", and that is exactly the difference the subject was
# missing until 2026-09-20.
build_pair() {
    name="$1"; per="$2"
    repo="$work/$name"
    for module in demo other; do
        src="modules/$module/src/main/scala/Demo.scala"
        mkdir -p "$repo/$(dirname "$src")" "$repo/target/out/jvm/scala-3.3.5/symbolum-$module/scoverage-report"
    done
    (
        cd "$repo"
        git_q init
        for module in demo other; do
            printf 'object Demo {\n}\n' > "modules/$module/src/main/scala/Demo.scala"
        done
        git_q add -A
        git_q commit -m base
    )

    for module in demo other; do
        src="$repo/modules/$module/src/main/scala/Demo.scala"
        {
            echo 'object Demo {'
            i=1
            while [ "$i" -le "$per" ]; do
                echo "  def f$i(): Int = $i"
                i=$((i + 1))
            done
            echo '}'
        } > "$src"
        {
            echo '<scoverage statement-count="'"$per"'" timestamp="'"$stamp"'">'
            i=1
            while [ "$i" -le "$per" ]; do
                echo '<statement source="'"$src"'" line="'$((i + 1))'" invocation-count="1">'
                echo '</statement>'
                i=$((i + 1))
            done
            echo '</scoverage>'
        } > "$repo/target/out/jvm/scala-3.3.5/symbolum-$module/scoverage-report/scoverage.xml"
    done
    (
        cd "$repo"
        git_q add -A
        git_q commit -m change
    )
    age "$repo"
}

run_subject() {
    status=0
    report=$(cd "$work/$1" && shift && sh "$subject" "$@" 2>&1) || status=$?
}

echo "$harness_name: the figure, the floor, and the two readings that are not a figure"

# 1. WELL COVERED. Twenty statements, all executed: the rate is 100 and the step is green.
build well 20 20
run_subject well HEAD~1
holds "a fully covered change reports every statement" "20 of 20 statement(s)"
holds "and reads as 100" "= 100.00%"
check "and exits green" "$status" "0"

# 2. THE DEFECT THE GATE IS FOR. Twenty statements, twelve executed: 60%, and red.
build poorly 20 12
run_subject poorly HEAD~1
holds "a poorly covered change reports the shortfall" "12 of 20 statement(s)"
holds "and reads as 60" "= 60.00%"
holds "and names the statements nobody executed" "not executed\|BELOW the floor"
check "and exits red" "$status" "1"

# 3. THE SAME AMOUNT OF CODE, ABOVE THE FLOOR, must not be red -- which is the half of the
# closure criterion that keeps case 2 from being satisfied by a gate that fails on size.
build enough 20 19
run_subject enough HEAD~1
holds "the same amount of code above the floor reports 95" "= 95.00%"
check "and exits green" "$status" "0"

# 4. TOO FEW STATEMENTS TO JUDGE. Four statements with one missed is 75%, which is under the
# floor and is not evidence of anything: the subject reports it and does not fail.
build tiny 4 3
run_subject tiny HEAD~1
holds "a change too small to judge says so" "reported and not judged"
holds "and still prints the rate" "= 75.00%"
check "and exits green" "$status" "0"

# 5. NOTHING TO MEASURE, which must not read like case 1. A change to a file outside
# `src/main` moves no statement the floors count, and the subject has to say that rather than
# print a rate over an empty set.
build untouched 20 20
(
    cd "$work/untouched"
    echo 'a note' > README.md
    git_q add -A
    git_q commit -m docs
)
run_subject untouched HEAD~1
holds "a change under no module says there is nothing to measure" "nothing to measure"
lacks "and does not print a rate" "%"
check "and exits green" "$status" "0"

# 6. CHANGED LINES WITH NO STATEMENT ON THEM, in a file the report does list: a comment, a blank,
# a signature. That is ordinary and is not a rate over an empty set, so the subject says which of
# the readings a reader has to rule out and exits green, because failing here would fail every
# change to a comment. Until 2026-09-24 this case was a report listing nothing at all, which the
# subject passed the same way; that report is refused now, and case 13 is where.
build comments 20 20
(
    cd "$work/comments"
    { echo '// a note'; cat modules/demo/src/main/scala/Demo.scala; } > next
    mv next modules/demo/src/main/scala/Demo.scala
    git_q add -A
    git_q commit -m note
)
{
    echo '<scoverage statement-count="20" timestamp="'"$stamp"'">'
    i=1
    while [ "$i" -le 20 ]; do
        echo '<statement source="'"$work/comments/modules/demo/src/main/scala/Demo.scala"'" line="'$((i + 2))'" invocation-count="1">'
        echo '</statement>'
        i=$((i + 1))
    done
    echo '</scoverage>'
} > "$work/comments/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
age "$work/comments"
run_subject comments HEAD~1
holds "lines with no statement in any report are not called covered" "none of those lines carries a statement"
holds "and the reader is told a stale report looks the same" "stale report"
check "and exits green" "$status" "0"

# 7. NO REPORT AT ALL is not the same as a report saying nothing, and is the one state the
# subject refuses outright: there is nothing to have an opinion about.
build missing 20 20
rm -rf "$work/missing/target/out/jvm/scala-3.3.5/symbolum-demo"
run_subject missing HEAD~1
holds "no report at all is refused rather than passed" "no coverage report on disk"
check "and exits 2, which is neither" "$status" "2"

# 8. THE FLOOR IS THE ONE THING A CALLER MAY MOVE, and moving it has to move the verdict, or
# every case above is about a constant rather than about a comparison.
build borderline 20 18
status=0
report=$(cd "$work/borderline" && COVERAGE_DELTA_MIN=95 sh "$subject" HEAD~1 2>&1) || status=$?
holds "90 of the statements is below a floor of 95" "= 90.00%"
check "and exits red at that floor" "$status" "1"
status=0
report=$(cd "$work/borderline" && COVERAGE_DELTA_MIN=85 sh "$subject" HEAD~1 2>&1) || status=$?
check "and green at a floor of 85" "$status" "0"

# 9. THE THREE WAYS THERE IS NO BASE, which are three answers and not one. On a runner the first
# is `github.event.before` on the first push to a ref, which is forty zeros; the third is a base a
# shallow clone does not hold. The empty string was what `ci.yml` passed on a manual run until
# 2026-09-24, when the choice of base moved into the script (case 15); it is still refused, since
# naming no base and naming an empty one are different mistakes.
build bases 20 20

status=0
report=$(cd "$work/bases" && sh "$subject" 0000000000000000000000000000000000000000 2>&1) || status=$?
holds "forty zeros is the first push on a ref and is not a failure" "no base revision"
check "and exits green" "$status" "0"

status=0
report=$(cd "$work/bases" && sh "$subject" "" 2>&1) || status=$?
holds "an empty base is a caller whose expression resolved to nothing" "empty string"
check "and is refused rather than silently defaulted" "$status" "2"

status=0
report=$(cd "$work/bases" && sh "$subject" beefbeefbeefbeefbeefbeefbeefbeefbeefbeef 2>&1) || status=$?
holds "a base that does not resolve names the shallow clone it usually is" "fetch-depth: 0"
check "and is refused" "$status" "2"

# The control on the three above: with no argument at all the subject measures `HEAD~1` and says
# something about the change, which is what keeps the three refusals from being a subject that
# refuses everything.
status=0
report=$(cd "$work/bases" && sh "$subject" 2>&1) || status=$?
holds "no argument at all still measures the last commit" "20 of 20 statement(s)"
check "and exits green" "$status" "0"

# 10. A PARTIAL SET OF REPORTS, which is the defect the verification of card 32c9a285 found on
# 2026-09-20 in the subject itself: it read the reports it found, knew nothing of how many to
# expect, and after a narrow run printed 9 of 9 statements at 100.00% for a change of 176 lines
# across eight modules. The population it had measured was one module and no line of the output
# named it, which is the same shape as the defect the whole tool is for.
#
# The criterion is the change and not the build: a module with no changed line hides nothing by
# not reporting. So the pair of cases is the control and the defect, in that order.
build_pair pair 20
run_subject pair HEAD~1
holds "a change over two modules that both report is measured over both" "40 of 40 statement(s)"
holds "and says so before the rate" "every one of the 2 module(s) it touches has a report"
check "and exits green" "$status" "0"

rm -rf "$work/pair/target/out/jvm/scala-3.3.5/symbolum-other"
run_subject pair HEAD~1
holds "a module with changed lines and no report is named" "other"
holds "and the subject refuses to rate the change over the rest" "invisible here"
check "and exits 2 rather than reporting a rate over part of the change" "$status" "2"
lacks "and prints no rate at all" "%"

# The control that keeps case 10 from being a rule about the number of reports: a module that did
# not report and carries NO changed line is not a shortfall, because nothing of it is in the
# figure to begin with. Without this the check would refuse every measurement taken after a narrow
# run of the one module a change touches, which is a legitimate local use.
build_pair quiet 20
(
    cd "$work/quiet"
    printf 'object Demo {\n  def g(): Int = 1\n}\n' > modules/demo/src/main/scala/Demo.scala
    git_q add -A
    git_q commit -m "only demo moves"
)
age "$work/quiet"
rm -rf "$work/quiet/target/out/jvm/scala-3.3.5/symbolum-other"
run_subject quiet HEAD~1
holds "a module that did not report and did not change is not a shortfall" "1 module(s) it touches has a report"
check "and the change is measured" "$status" "0"

# 11 TO 15 ARE THE VERIFICATION OF CARD 2cc13929, 2026-09-24: five things the subject answered
# wrongly, each measured then and each a case here that fails on the subject of that day.

# 11. A CHANGED FILE NO REPORT LISTS. The report is of `Demo.scala`; the change also adds
# `Other.scala`, twenty-two lines of code nobody's report mentions. The subject read "20 of 20 =
# 100.00%" and exited green, which is a rate over part of the change presented as the change.
build unlisted 20 20
(
    cd "$work/unlisted"
    {
        echo 'object Other {'
        i=1
        while [ "$i" -le 21 ]; do echo "  def g$i(): Int = $i"; i=$((i + 1)); done
    } > modules/demo/src/main/scala/Other.scala
    git_q add -A
    git_q commit --amend -m change
)
age "$work/unlisted"
run_subject unlisted HEAD~1
holds "a changed file in no report is named" "Other.scala"
lacks "and no rate is printed over the file that is listed" "20 of 20"
check "and the change is refused as unmeasured" "$status" "2"

# 12. AN UNCOMMITTED EDIT ABOVE THE CHANGE. The report is built from the working tree, where a
# comment now sits above the twenty new statements, so they are on lines 3 to 22; the committed
# change has them on 2 to 21. Diffing to HEAD read the committed numbers against the working
# tree's report.
build dirty 20 20
(
    cd "$work/dirty"
    { echo '// not committed'; cat modules/demo/src/main/scala/Demo.scala; } > next
    mv next modules/demo/src/main/scala/Demo.scala
)
{
    echo '<scoverage statement-count="20" timestamp="'"$stamp"'">'
    i=1
    while [ "$i" -le 20 ]; do
        hits=1; [ "$i" -eq 20 ] && hits=0
        echo '<statement source="'"$work/dirty/modules/demo/src/main/scala/Demo.scala"'" line="'$((i + 2))'" invocation-count="'"$hits"'">'
        echo '</statement>'
        i=$((i + 1))
    done
    echo '</scoverage>'
} > "$work/dirty/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
age "$work/dirty"
run_subject dirty HEAD~1
holds "the change is read in the working tree's coordinates, all twenty statements" "19 of 20 statement(s)"
holds "including the one on the last line that nobody ran" "= 95.00%"
check "and exits green" "$status" "0"

# 12b. The same, with the edit a NEW FILE git does not know yet: it is part of the change.
build fresh 20 20
(
    cd "$work/fresh"
    printf 'object Fresh {\n  def h(): Int = 1\n}\n' > modules/demo/src/main/scala/Fresh.scala
)
age "$work/fresh"
run_subject fresh HEAD~1
holds "an untracked source is part of the change and is named when no report lists it" "Fresh.scala"
check "and is refused rather than left out" "$status" "2"

# 13. A REPORT NO BUILD WROTE. The shared checkout held `<statements/>`, fourteen bytes dated 2020,
# in every module, and the subject passed a change of 199 lines over them.
build stub 20 20
printf '<statements/>' > "$work/stub/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
run_subject stub HEAD~1
holds "a report with no timestamp is named as not a build's" "no build of scoverage wrote them"
check "and refused" "$status" "2"

# 13b. A report OLDER than a changed file, which is a report of a tree without the change.
build older 20 20
touch -t 202512010000 "$work/older/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
run_subject older HEAD~1
holds "a changed file newer than its module's report is named" "changed after their module's report"
check "and refused" "$status" "2"

# 14. THE NEWEST DATE, read as a number. Reports stamped the 3rd and the 22nd of September; the
# subject sorted `ls -l` columns as text and printed the 3rd.
build_pair dated 20
sept3=$(( $(date -u -d '2026-09-03 12:00' +%s 2>/dev/null || date -u -j -f '%Y-%m-%d %H:%M' '2026-09-03 12:00' +%s) * 1000 ))
sept22=$(( $(date -u -d '2026-09-22 12:00' +%s 2>/dev/null || date -u -j -f '%Y-%m-%d %H:%M' '2026-09-22 12:00' +%s) * 1000 ))
for pair in "demo $sept3 202609031200" "other $sept22 202609221200"; do
    set -- $pair
    file="$work/dated/target/out/jvm/scala-3.3.5/symbolum-$1/scoverage-report/scoverage.xml"
    sed "s/timestamp=\"[0-9]*\"/timestamp=\"$2\"/" "$file" > "$file.next" && mv "$file.next" "$file"
    touch -t "$3" "$file"
done
run_subject dated HEAD~1
holds "the newest of the two reports is the one printed" "2026-09-22"
lacks "and not the earlier one" "2026-09-03"
check "and exits green" "$status" "0"

# 15. THE EVENT A RUNNER IS ON, decided here and not in YAML. `ci.yml` passed
# `github.event.before || github.event.pull_request.base.sha`: empty on a manual run, so exit 2 on
# every one, and on a pull request's synchronize the previous push rather than the base.
build events 20 20
status=0
report=$(cd "$work/events" && sh "$subject" --event workflow_dispatch "" "" 2>&1) || status=$?
holds "a manual run names no change and says so" "names no change"
check "and is not a red job" "$status" "0"

status=0
report=$(cd "$work/events" && sh "$subject" --event pull_request beefbeefbeefbeefbeefbeefbeefbeefbeefbeef HEAD~1 2>&1) || status=$?
holds "a pull request is measured from its base and not from the previous push" "20 of 20 statement(s)"
check "and exits green" "$status" "0"

status=0
report=$(cd "$work/events" && sh "$subject" --event push HEAD~1 beefbeefbeefbeefbeefbeefbeefbeefbeefbeef 2>&1) || status=$?
holds "a push is measured from the commit before it" "20 of 20 statement(s)"
check "and exits green" "$status" "0"

# 16. A REPORT WRITTEN AFTER THE EDIT FROM INSTRUMENTATION WRITTEN BEFORE IT. The verification of
# card 61cdee9d, 2026-09-25, on a real report of `scan` at 570e1e40: an uncommitted line inserted
# above the change, then `coverage scan/coverageReport` alone, which rewrites `scoverage.xml` from
# the `scoverage.coverage` the last compile left and recompiles nothing. The report is newer than
# every changed file, so 13b does not fire, and its statements are in the coordinates of the file
# before the edit: the subject answered "none of those lines carries a statement", exit 0, on a
# change of six statements of which two were never run. A report's mtime says when it was
# written, not what it was built from.
build replayed 20 20
data="$work/replayed/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-data"
mkdir -p "$data"
printf 'instrumentation of the tree before the edit\n' > "$data/scoverage.coverage"
touch -t 202601010000 "$data/scoverage.coverage"
{
    echo '// an uncommitted line above the change'
    cat "$work/replayed/modules/demo/src/main/scala/Demo.scala"
} > "$work/replayed/demo.next" && mv "$work/replayed/demo.next" "$work/replayed/modules/demo/src/main/scala/Demo.scala"
touch -t 202601020000 "$work/replayed/modules/demo/src/main/scala/Demo.scala"
touch -t 202601030000 "$work/replayed/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-report/scoverage.xml"
run_subject replayed HEAD~1
holds "a changed file newer than the instrumentation its report was written from is named" "Demo.scala"
holds "and the reason is the compile, not the report" "instrumented compile"
check "and refused" "$status" "2"

# 16b. A REPORT WITH NO INSTRUMENTATION BESIDE IT, which no build of scoverage leaves: the date of
# the compile is what 16 reads, and without it there is nothing to compare, so the subject refuses
# rather than falling back on the report's own date, which is the reading 16 shows is not enough.
build bare 20 20
rm -rf "$work/bare/target/out/jvm/scala-3.3.5/symbolum-demo/scoverage-data"
run_subject bare HEAD~1
holds "a report with no instrumentation is named" "no instrumentation beside them"
check "and refused" "$status" "2"
lacks "and no rate is printed" "%"

summarise
