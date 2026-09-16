# Sourced by the tests beside it. Not executable, and it runs nothing on its own.
#
# It exists because there are two of them. One test carrying its own four helpers is a file; two
# carrying the same four is the first copy, and the copy that matters here is `git_q`, whose whole
# point is that a broken fixture must not read as a passing suite. A second copy of that reasoning
# is a second place for it to be got wrong quietly.
#
# A sourcing test must set `failures=0` before its first check and exit non-zero when it ends above
# zero; `summarise` does the second half.

# A named check rather than `set -e` on a comparison: every case runs, so one broken shape does not
# hide the state of another, and the name is what a pipeline log is read for.
check() {
    if [ "$2" = "$3" ]; then
        echo "  ok    $1"
    else
        echo "  FAIL  $1"
        echo "          expected: $3"
        echo "          actual:   $2"
        failures=$((failures + 1))
    fi
}

# Both read `$report`, which the sourcing test sets, because every assertion here is about one run
# and passing it round would be the same string spelled twice per line.
holds() {
    if printf '%s\n' "$report" | grep -q "$2"; then
        echo "  ok    $1"
    else
        echo "  FAIL  $1: no line matching /$2/"
        failures=$((failures + 1))
    fi
}

lacks() {
    if printf '%s\n' "$report" | grep -q "$2"; then
        echo "  FAIL  $1: a line matches /$2/"
        printf '%s\n' "$report" | grep "$2" | sed 's|^|          |'
        failures=$((failures + 1))
    else
        echo "  ok    $1"
    fi
}

# Quiet while it works and loud when it does not. Discarding both streams is what a fixture step
# usually does, and it cost a debugging pass: a `git clone` run from a directory the test had just
# deleted failed, `set -e` stopped the run at exit 128, and the output ended mid-list with every
# printed check passing. A fixture that breaks must not read as a suite that ended.
git_q() {
    if ! git_out=$(git -c user.email=test@invalid -c user.name=test -c commit.gpgsign=false \
        -c advice.detachedHead=false -c init.defaultBranch=7.0 "$@" 2>&1); then
        echo "${harness_name:-test}: the fixture could not be built: git $*" >&2
        printf '%s\n' "$git_out" | sed 's|^|    |' >&2
        exit 2
    fi
}

summarise() {
    echo
    if [ "$failures" -eq 0 ]; then
        echo "${harness_name:-test}: every check passed"
        exit 0
    fi
    echo "${harness_name:-test}: $failures check(s) failed"
    exit 1
}
