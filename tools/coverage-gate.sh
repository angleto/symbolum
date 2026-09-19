#!/bin/sh
# Run the coverage gate, and say which of three things happened rather than leaving one of them
# silent.
#
# WHY THIS EXISTS. The gate is `clean coverage test coverageReport`, a SEQUENCE, and sbt stops at
# the first command that fails. So `coverageReport` does not run when `test` is red, and the log
# says nothing about the floors having gone unasked: sixteen minutes and forty-six seconds of a
# run that did not measure the thing it was launched for, reading as a test failure. Measured
# again on 2026-09-19 in a second shape, a run killed at `sbt-exit = 143` after nine of ten
# modules had reported: `grep -icE "coveragereport|coverage minimum|scoverage"` over its 4068
# lines of log returned **0**, against 11 for the run that finished twenty minutes later.
#
# **The absence of `Coverage is below` is not a pass, it is an instrument that did not read.** A
# reader who greps for that line and does not find it concludes the floors held, and in both
# shapes above the floors neither held nor fell: they were never asked. That is the distinction
# `Refutation` keeps between seven answers one floor down, and this file is it at the build.
#
# THE THREE ANSWERS, which is the whole of what this adds:
#
#   - the floors were asked and they held
#   - the floors were asked and one fell            (sbt says which; the reports are on disk)
#   - THE FLOORS WERE NEVER ASKED                   (a red suite, or a run that did not finish)
#
# WHAT DECIDES WHICH, and it is not the exit code. A report is written per module by
# `coverageReport`, so a report of this run's own vintage is the evidence that the command ran at
# all. The exit code then separates the first two. Read the other way round the exit code says
# nothing: a run killed before `coverageReport` and a run whose floor fell are both non-zero.
#
# WHAT IT DOES NOT DO. It does not rerun anything, it does not lower a floor, and it does not
# recover a lost measurement. `tools/sbt coverage coverageReport` without `clean` and without
# `test` builds the report from whatever instrumented data is on disk, which is how a run that
# died in `tactics` is salvaged; that is a thing to do by hand, with the checks card f18d03d2
# lists, and not something a gate should do behind a reader's back.
#
# `tools/coverage-gate-test.sh` holds every branch of this against stubs, and CI runs it.

set -u

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/.." && pwd)

# The build tool is asked for through `tools/sbt`, which is where the decision about the machine's
# cap lives. Overridable so the test beside this can hand it a stub; the variable is read nowhere
# else and is not a thing a person uses.
SBT="${COVERAGE_GATE_SBT:-$here/sbt}"

# A marker file rather than a timestamp in a variable, because `find -newer` compares against a
# file and every shell's `stat` spells the other comparison differently. It is created before the
# build and is what "of this run's own vintage" means.
marker=$(mktemp) || { echo "coverage-gate: cannot create a marker file" >&2; exit 2; }
cleanup() { rm -f "$marker"; }

# WHICH MODULES ARE EXPECTED, asked of the disk rather than read from a list, for the reason
# `fatalWarnings` gives about the same question: a module added without an entry in a list is
# exactly the module nobody notices is unmeasured. Every directory under `modules/` with a
# `src/main` produces a report; `aggregate` has no sources and produces none.
expected() {
    _n=0
    for _d in "$root"/modules/*/; do
        [ -d "$_d/src/main" ] || continue
        _n=$((_n + 1))
    done
    echo "$_n"
}

fresh() {
    # why: `find` prints nothing and exits non-zero when `modules/` does not exist, which is a
    # checkout this script has no business running in; the count of zero is the right answer and
    # is reported as "never asked" below, which names the situation better than a stack of errors.
    find "$root"/modules/*/target/scala-*/scoverage-report/scoverage.xml \
        -newer "$marker" 2>/dev/null | grep -c . || :
}

# THE VERDICT IS PRINTED ON EVERY PATH, including the signal paths, which is the half that covers
# a run the supervising harness takes away. Without the trap, the one shape where the answer is
# most needed -- the run that did not finish -- is the one shape that prints nothing.
verdict() {
    _got=$(fresh)
    _want=$(expected)
    echo
    echo "coverage-gate: ------------------------------------------------------------"
    if [ "$_got" -eq 0 ]; then
        echo "coverage-gate: THE FLOORS WERE NEVER ASKED. No module wrote a coverage report in"
        echo "coverage-gate: this run, so \`coverageReport\` did not run: the sequence stopped"
        echo "coverage-gate: before it. This is NOT a pass and is not a floor falling; nothing"
        echo "coverage-gate: about coverage was measured. Look above for a red suite, or for a"
        echo "coverage-gate: log that ends mid-sentence because the run was killed."
        echo "coverage-gate: To build the report from the data already on disk, without paying"
        echo "coverage-gate: for the suite again: tools/sbt coverage coverageReport"
    elif [ "$_got" -lt "$_want" ]; then
        echo "coverage-gate: THE FLOORS WERE ASKED OF $_got MODULE(S) OF $_want. The run did not"
        echo "coverage-gate: reach the end, so the modules with no report of this vintage were"
        echo "coverage-gate: not measured and are not passing. Whatever verdict appears above is"
        echo "coverage-gate: about the $_got that reported."
    elif [ "$status" -eq 0 ]; then
        echo "coverage-gate: the floors were asked of all $_want modules and they held."
    else
        echo "coverage-gate: the floors were asked of all $_want modules and the build exited"
        echo "coverage-gate: $status. A floor fell: the line above names the rate and the floor,"
        echo "coverage-gate: and modules/*/target/scala-*/scoverage-report/ says which module."
    fi
    echo "coverage-gate: ------------------------------------------------------------"
}

# `status` is set before the traps can fire so that a signal arriving during the build finds it
# defined under `set -u`. 143 is what a SIGTERM leaves, which is the code the run measured on
# 2026-09-19 came back with.
status=143
on_signal() {
    echo "coverage-gate: interrupted" >&2
    verdict
    cleanup
    exit 143
}
trap on_signal INT TERM

"$SBT" clean coverage test coverageReport
status=$?

verdict
cleanup
exit "$status"
