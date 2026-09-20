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

# A repository with one module, a first commit, and then a change of `$1` statements of which
# `$2` are recorded as executed. The report is written by hand: the subject reads the numbers it
# finds, and a fixture that ran a real build would be measuring scoverage rather than this.
build() {
    name="$1"; added="$2"; covered="$3"
    repo="$work/$name"
    src="modules/demo/src/main/scala/Demo.scala"
    mkdir -p "$repo/$(dirname "$src")" "$repo/modules/demo/target/scala-3.3.5/scoverage-report"
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
        echo '<scoverage statement-count="'"$added"'">'
        i=1
        while [ "$i" -le "$added" ]; do
            hits=0
            [ "$i" -le "$covered" ] && hits=1
            echo '<statement source="'"$repo/$src"'" line="'$((i + 1))'" invocation-count="'"$hits"'">'
            echo '</statement>'
            i=$((i + 1))
        done
        echo '</scoverage>'
    } > "$repo/modules/demo/target/scala-3.3.5/scoverage-report/scoverage.xml"
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
        mkdir -p "$repo/$(dirname "$src")" "$repo/modules/$module/target/scala-3.3.5/scoverage-report"
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
            echo '<scoverage statement-count="'"$per"'">'
            i=1
            while [ "$i" -le "$per" ]; do
                echo '<statement source="'"$src"'" line="'$((i + 1))'" invocation-count="1">'
                echo '</statement>'
                i=$((i + 1))
            done
            echo '</scoverage>'
        } > "$repo/modules/$module/target/scala-3.3.5/scoverage-report/scoverage.xml"
    done
    (
        cd "$repo"
        git_q add -A
        git_q commit -m change
    )
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

# 6. THE CONTROL ON THE REPORT, and it is the one that separates this from a subject that has
# stopped reading. Lines were added and no report mentions them: that is what a stale report
# gives, and the subject must refuse to read it as a pass while still exiting green, because
# failing here would fail every documentation change.
build stale 20 20
rm -f "$work/stale/modules/demo/target/scala-3.3.5/scoverage-report/scoverage.xml"
printf '<scoverage statement-count="0">\n</scoverage>\n' \
    > "$work/stale/modules/demo/target/scala-3.3.5/scoverage-report/scoverage.xml"
run_subject stale HEAD~1
holds "lines with no statement in any report are not called covered" "none of those lines carries a statement"
holds "and the reader is told a stale report looks the same" "stale report"
check "and exits green" "$status" "0"

# 7. NO REPORT AT ALL is not the same as a report saying nothing, and is the one state the
# subject refuses outright: there is nothing to have an opinion about.
build missing 20 20
rm -rf "$work/missing/modules/demo/target"
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

# 9. THE THREE WAYS THERE IS NO BASE, which are three answers and not one. Only the middle of
# them can be produced on a runner, and none of them can be produced by reading the script: the
# caller in `.github/workflows/ci.yml` passes `github.event.before || ...`, which is forty zeros
# on the first push to a ref, the base sha on a pull request, and an empty string when neither
# expression resolves.
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

rm -rf "$work/pair/modules/other/target"
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
rm -rf "$work/quiet/modules/other/target"
run_subject quiet HEAD~1
holds "a module that did not report and did not change is not a shortfall" "1 module(s) it touches has a report"
check "and the change is measured" "$status" "0"

summarise
