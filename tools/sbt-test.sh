#!/bin/sh
# Run `tools/sbt` against a stub wrapper and a stub build tool, in the four states it can be in.
#
# WHY STUBS AND NOT THE REAL ONES. The subject's whole content is a decision about which of two
# programs to exec and what to say about it. The real wrapper belongs to a practice that is not
# part of this repository: it is absent from every clone and from every runner, so a test that
# needed it would only ever run on one laptop, which is the condition the subject exists to
# remove. The real `sbt` is worse again, since invoking it is minutes and a network. Both are
# replaced by scripts that print what they were handed, which is exactly the contract asserted:
# the wrapper is exec'd with `--`, then `sbt`, then the caller's arguments untouched.
#
# WHY THE `PATH` IS REBUILT RATHER THAN PREPENDED TO. The fall-through execs `sbt` by name, so the
# stub has to be found by the same lookup the real one would be. Prepending would leave the real
# `sbt` reachable if the stub were ever not created, and a test that silently invokes the real
# build tool is one that hangs for minutes and then passes for the wrong reason.
#
# WHAT IT DOES NOT COVER. Whether the real wrapper serialises anything, which is its own business
# and its own tests; and whether `sbt` is on the PATH at all, which is a machine's problem and not
# a decision this file makes.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/sbt"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=sbt-test
. "$here/test-harness.sh"

failures=0

# Every run below ends `|| true` under a `set -e` script, and that is not laziness. A subject that
# DIES instead of falling through — `exec`ing something it should have rejected, so the shell exits
# 126 and never reaches `sbt` — would otherwise abort this file mid-list with no failure named, and
# a check whose failure has to be decoded is one somebody re-runs to see whether it is real. Found
# by perturbation: relaxing the subject's `-x` to `-e` produced exactly that, a non-zero suite with
# nothing printed. The status is not what is being asserted here; the two cases where it is assert
# it explicitly at the bottom.
#
# The stubs. Each prints one line naming itself and every argument it was given, so an assertion
# can tell "the wrapper ran and handed the build tool the arguments" from "the build tool ran".
mkdir -p "$work/bin"
cat > "$work/bin/sbt" <<'STUB'
#!/bin/sh
echo "STUB-SBT $*"
STUB
cat > "$work/wrapper" <<'STUB'
#!/bin/sh
echo "STUB-WRAPPER $*"
STUB

# A second wrapper that also RUNS what it was handed, which the echoing one deliberately does not.
# The routing assertions want one that swallows the command, so that "the build tool was reached"
# can only mean the subject bypassed the wrapper; the exit-status assertion wants one that passes
# the status back, which is what a real wrapper does. One stub cannot be both, and trying to make
# it both is how the status assertion was vacuous when this file was first written: it expected 0
# from a stub that could only ever give 0, so a subject that swallowed the status passed it.
# Perturbation found that and nothing else would have.
cat > "$work/wrapper-exec" <<'STUB'
#!/bin/sh
echo "STUB-WRAPPER $*"
shift                 # the `--`, which is the wrapper's to consume
exec "$@"
STUB
chmod +x "$work/bin/sbt" "$work/wrapper" "$work/wrapper-exec"
PATH="$work/bin:/usr/bin:/bin"
export PATH

# A tree of its own rather than this one, so that nothing the developer happens to have configured
# can decide the result.
mkdir -p "$work/tree/tools"
cp "$subject" "$work/tree/tools/sbt"
chmod +x "$work/tree/tools/sbt"
run="$work/tree/tools/sbt"

# 1. Nothing named. The build runs, the wrapper does not, and the subject SAYS the build is
#    uncapped. That last one is **a decision and not a preference**, taken on 2026-09-17 after two
#    sessions had walked into each other's positions on it, so this check is what holds it rather
#    than what argues for it: silence here would be tidier and would go red.
#
#    The case for silence is that a line on every build of every clone with no such practice
#    around it is noise. The case for the line is the repository's own doctrine one floor down:
#    `Refutation` keeps seven answers apart and `LogicError.Standing` three, and both say in
#    writing that merging two of them turns "I could not ask" into "I asked and it was fine". A
#    silent fall-through is that merge, and the file is called `tools/sbt`, so a reader who takes
#    the name for the cap is reading it as written. `tools/sbt` carries the argument; this carries
#    the consequence.
report=$(SYMBOLUM_BUILD_WRAPPER= "$run" test 2>&1 || true)
holds "unnamed: the build runs" "STUB-SBT test"
lacks "unnamed: the wrapper does not" "STUB-WRAPPER"
holds "unnamed: and it says the build is uncapped" "nothing is capping this build"

# 2. The environment names a usable wrapper. It is exec'd with `--`, then the build tool, then the
#    caller's arguments untouched. The `--` is asserted rather than tolerated: it is what leaves a
#    wrapper room for options of its own, and without an assertion it reads like punctuation
#    somebody could tidy away.
report=$(SYMBOLUM_BUILD_WRAPPER="$work/wrapper" "$run" clean coverage test 2>&1 || true)
holds "named: the wrapper gets the build tool and the arguments" "STUB-WRAPPER -- sbt clean coverage test"
lacks "named: the build tool is not also reached directly" "STUB-SBT"
lacks "named: and nothing is announced" "nothing is capping this build"

# 3. Named and absent. This is where somebody MEANT to be under the cap and is not, so the line
#    carries the path as well: telling them the variable is unset would send them to configure the
#    thing they already configured. The build still runs, because refusing would turn a
#    misconfigured machine into one that cannot build at all.
report=$(SYMBOLUM_BUILD_WRAPPER="$work/not-there" "$run" test 2>&1 || true)
holds "absent: the build still runs" "STUB-SBT test"
holds "absent: and the path is named" "$work/not-there"
holds "absent: and it says the build is uncapped" "nothing is capping this build"
lacks "absent: not reported as unset" "is unset"

# 4. Present and not executable, which is the same state to a reader and a DIFFERENT one to the
#    shell. It is here because perturbation said so: relaxing the subject's `-x` to `-e` passed
#    every check above, since a path that does not exist fails both tests and takes the same
#    branch either way. The two are only told apart by a file that is there and cannot run, which
#    is also the likelier mistake in life — a wrapper copied without its mode, or on a filesystem
#    mounted without exec.
cat > "$work/unrunnable" <<'STUB'
#!/bin/sh
echo "STUB-WRAPPER $*"
STUB
chmod -x "$work/unrunnable"
report=$(SYMBOLUM_BUILD_WRAPPER="$work/unrunnable" "$run" test 2>&1 || true)
holds "unrunnable: the build still runs" "STUB-SBT test"
holds "unrunnable: and the path is named" "$work/unrunnable"
lacks "unrunnable: and it is not exec'd" "STUB-WRAPPER"

# The exit status is the build's in both shapes, or a caller cannot tell a failed build from a
# subject that lost it.
#
# These two are the weakest pair here and are labelled rather than dressed up: `exec` and `set -e`
# both defend the property, so the obvious perturbations do not produce a version that fails these
# and nothing else. Dropping the `exec` for a call plus `exit 0` still exits 3, because `set -e`
# stops the script first; `|| true` falls through to the unnamed branch and is caught by the
# routing assertions above. What they do guard is somebody deliberately normalising the status
# later, and what makes them worth keeping is the vacuity described beside the second stub.
cat > "$work/bin/sbt" <<'STUB'
#!/bin/sh
exit 3
STUB
chmod +x "$work/bin/sbt"
status=0
SYMBOLUM_BUILD_WRAPPER= "$run" test >/dev/null 2>&1 || status=$?
check "unnamed: the build's exit status survives" "$status" "3"
status=0
SYMBOLUM_BUILD_WRAPPER="$work/wrapper-exec" "$run" test >/dev/null 2>&1 || status=$?
check "named: the build's exit status survives the wrapper" "$status" "3"

summarise
