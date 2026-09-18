#!/bin/sh
# Run `tools/scaladoc-scope.sh` against generated documentation built for the purpose, one page
# per answer it can give.
#
# WHY FIXTURES AND NOT THE REAL API DIRECTORY. The subject reads `modules/*/target`, which is build
# output: it exists on a machine that has just run `sbt clean doc` and on no runner that has not.
# A test that needed it would be a test that runs after a ten-minute build or not at all, and the
# half worth checking every time is the classification, which is decided by four shapes of `href`
# and needs no compiler to exhibit. The real documentation is what the gate in
# `.github/workflows/ci.yml` points the subject at, and the two are different jobs on purpose.
#
# WHY THE OFF-SCOPE CASE IS NOT THE ONLY ONE. A check that only ever sees its own defect passes by
# being blind: three of the four shapes below are links this repository writes by the hundred, and
# a subject that flagged them would be red on a tree with nothing wrong with it. The measurement
# that chose them is on the real tree at `d247b58` on 2026-09-18: of 912 unqualified queries, 656
# resolved to
# the writer's own entity, 25 to a member it inherits, 231 to a top-level entity, and none
# anywhere else. Each of the first three is a case here, and dropping any one of them would turn
# a green run into hundreds of false reports.
#
# WHAT IT DOES NOT COVER. Whether scaladoc emits the markup assumed here, which is a fact about
# the tool and changes with its version: the shapes below were copied from the output of scaladoc
# 3.3.5 on 2026-09-18. The subject's own docstring carries what it cannot see in the real tree,
# which is every query scaladoc did not publish.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/scaladoc-scope.sh"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=scaladoc-scope-test
. "$here/test-harness.sh"

failures=0

api="$work/modules/demo/target/scala-3.3.5/api/garden/xeno/demo"
mkdir -p "$api"

# A page with a member of its own, which is what an unqualified query is for. The member table
# entry carries `class="documentableName"` and the doc body carries the link; both shapes are the
# subject's two passes over the same file.
cat > "$api/Writer.html" <<'HTML'
<div class="members">
  <a href="Writer.html#settle-abc" t="n" class="documentableName ">settle</a>
</div>
<div class="doc">
  <p>Its own member: <a href="Writer.html#settle-abc">settle</a>.</p>
  <p>A top-level entity of the module: <a href="Reader$.html">Reader</a>.</p>
  <p>A member it inherits, listed here under the declaring class:
     <a href="Base.html#legible-423">legible</a>.</p>
  <p>Nested inside itself: <a href="Writer$$Verdict.html">Verdict</a>.</p>
</div>
<div class="members">
  <a href="Base.html#legible-423" t="n" class="documentableName ">legible</a>
</div>
HTML

cat > "$api/Reader$.html" <<'HTML'
<div class="doc">
  <p>A qualified query renders with the dots the author wrote and is not this question:
     <a href="Writer$$Verdict.html">Writer.Verdict</a>.</p>
</div>
HTML

report=$(sh "$subject" "$work" 2>&1) || true
holds "an own member is in scope" 'every one in scope'
lacks "an own member is not reported" 'settle'
lacks "a top-level entity is not reported" '\[\[Reader\]\]'
lacks "an inherited member is not reported" '\[\[legible\]\]'
lacks "a nested entity is not reported" '\[\[Verdict\]\]'
holds "the count it read is printed" '4 unqualified'

# The defect this exists for: a name written in one entity that lands inside another. The page
# does not list `Problem` among its members, so nothing puts it in this writer's scope.
cat > "$api/Resolution.html" <<'HTML'
<div class="doc">
  <p>A refutation of that <a href="Cnf$$Problem.html">Problem</a>.</p>
</div>
HTML

report=$(sh "$subject" "$work" 2>&1) || true
holds "an off-scope query is reported" '\[\[Problem\]\] resolved to Cnf\$\$Problem.html'
holds "the report names the page" 'Resolution.html'
holds "the report says what to do" 'qualify it'
status=0
sh "$subject" "$work" >/dev/null 2>&1 || status=$?
check "an off-scope query fails the run" "$status" "1"

rm "$api/Resolution.html"

# A package page re-renders the brief of every member relative to the package, so every link in a
# member's docstring appears there a second time and every one of them looks off-scope. Reading it
# reported 47 of them on the real tree on 2026-09-18, all of them duplicates of links that are
# fine where they are actually written.
mkdir -p "$work/modules/demo/target/scala-3.3.5/api/garden/xeno/demo"
cat > "$work/modules/demo/target/scala-3.3.5/api/garden/xeno/demo.html" <<'HTML'
<div class="doc">
  <p>Brief of a member, re-rendered here: <a href="demo/Cnf$$Problem.html">Problem</a>.</p>
</div>
HTML

report=$(sh "$subject" "$work" 2>&1) || true
lacks "a package page is not read" '\[\[Problem\]\]'
holds "and the rest still is" 'every one in scope'

# Nothing to read is not a clean answer, which is how a census like this passes for free. The doc
# task is cached, so an incremental run documents only what recompiled.
empty=$(mktemp -d)
report=$(sh "$subject" "$empty" 2>&1) || true
holds "an empty tree is refused" 'read no query at all'
holds "and it names the repair" 'clean doc'
status=0
sh "$subject" "$empty" >/dev/null 2>&1 || status=$?
check "an empty tree fails the run" "$status" "1"
rm -rf "$empty"

summarise
