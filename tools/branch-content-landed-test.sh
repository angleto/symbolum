#!/bin/sh
# Run `branch-content-landed.sh` against a repository built for the purpose, one branch per answer.
#
# WHY THIS EXISTS. The script declares two shapes of name and for as long as it existed it extracted
# one. The two `sed` calls were grouped on one stdin, so the first consumed the stream to EOF and
# the second was handed nothing, and the dead one was the shape this file's own comment calls what a
# development exports: a lemma name written as a string. Nothing failed, because a branch whose
# names are all declarations is answered correctly and that is most branches; the wrong answer
# arrives only on a branch the other shape is the whole of, and it arrives as "introduces no name
# this can look for", which reads as a property of the branch.
#
# So the fixture is one branch per answer, and the branch that matters is the one whose only new
# name is a quoted one. `both-on-one-line` is the second: a line carrying a declaration AND a quoted
# name is what refutes the repair that suggests itself, chaining the two as `-e` expressions of one
# `sed`, since the first substitution rewrites the pattern space and the second reads the result.
#
# WHAT IT DOES NOT COVER. Whether the two shapes are the right two. A name this repository exports
# some third way is missed by the script and by this file alike, and the only instrument for that is
# somebody reading a diff the tool called empty.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/branch-content-landed.sh"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=branch-content-landed-test
. "$here/test-harness.sh"

failures=0

# The line, and one branch per answer the tool has:
#   quoted-only        adds a line whose only name is a quoted one, absent from the line
#   quoted-landed      the same shape, with the name already present in the line
#   declaration-only   adds a declaration, which is the shape that always worked
#   both-on-one-line   one added line carrying both shapes at once
#   nothing-scala      touches no Scala at all
#   orphan             no merge base with the line
build_fixture() {
    git_q init -b 7.0 "$work/repo"
    cd "$work/repo"
    mkdir -p src
    cat > src/Base.scala <<'SCALA'
object Base {
  val KNOWN = "ALREADY_IN_LINE"

  def run(): Unit = {
    ()
  }
}
SCALA
    git_q add src/Base.scala
    git_q commit -m "the line"

    add_line() {
        git_q checkout -b "$1" 7.0
        awk -v line="$2" '{ print } /^  def run/ { print line }' src/Base.scala > src/Base.next
        mv src/Base.next src/Base.scala
        git_q commit -am "$1"
        git_q checkout 7.0
    }

    add_line quoted-only '    register("NUM_PROBE_LEMMA")'
    add_line quoted-landed '    register("ALREADY_IN_LINE")'
    add_line declaration-only '  def probeThing(): Unit = ()'
    add_line both-on-one-line '  val probeHolder = "NUM_BOTH_LEMMA"'

    git_q checkout -b nothing-scala 7.0
    echo "a note" > NOTES.md
    git_q add NOTES.md
    git_q commit -m "no Scala here"
    git_q checkout 7.0

    git_q checkout --orphan orphan
    git_q rm -rf .
    mkdir -p src
    echo 'object Elsewhere { val OTHER = "NUM_ORPHAN_LEMMA" }' > src/Elsewhere.scala
    git_q add src/Elsewhere.scala
    git_q commit -m "a history of its own"
    git_q checkout 7.0
}

run_subject() {
    status=0
    report=$(cd "$work/repo" && sh "$subject" "$1" 7.0 2>&1) || status=$?
}

build_fixture

# The case the card is about and the one the tool was silent on: a branch whose whole contribution
# is a name written as a string.
run_subject quoted-only
echo "branch-content-landed, a branch whose only new name is quoted:"
check "quoted-only: refuses the deletion" "$status" "1"
holds "quoted-only: names the lemma it found" '^  NUM_PROBE_LEMMA$'
holds "quoted-only: counts it" '^1 of 1 name(s) are not in 7.0'
lacks "quoted-only: does not call the branch empty" 'introduces no name'

run_subject quoted-landed
echo "branch-content-landed, the same shape, already in the line:"
check "quoted-landed: allows the deletion" "$status" "0"
holds "quoted-landed: says what it checked" '^branch-content-landed: all 1 name(s)'
lacks "quoted-landed: does not call the branch empty" 'introduces no name'

# The shape that always worked, asserted so that reviving the other one is not paid for with it.
run_subject declaration-only
echo "branch-content-landed, a branch introducing a declaration:"
check "declaration-only: refuses the deletion" "$status" "1"
holds "declaration-only: names the declaration" '^  probeThing$'
holds "declaration-only: counts it" '^1 of 1 name(s) are not in 7.0'

# One line, both shapes. This is what refuses the repair of chaining the two expressions in one
# `sed`: there the first substitution replaces the line with `probeHolder` and the quoted name is
# gone before the second expression reads it.
run_subject both-on-one-line
echo "branch-content-landed, one added line carrying both shapes:"
check "both-on-one-line: refuses the deletion" "$status" "1"
holds "both-on-one-line: finds the declaration" '^  probeHolder$'
holds "both-on-one-line: finds the quoted name on the same line" '^  NUM_BOTH_LEMMA$'
holds "both-on-one-line: counts two, not one" '^2 of 2 name(s) are not in 7.0'

# The honest empty answer, which has to stay reachable: without this case, "introduces no name"
# could be removed altogether and every other check here would still pass.
run_subject nothing-scala
echo "branch-content-landed, a branch touching no Scala:"
check "nothing-scala: exits 0" "$status" "0"
holds "nothing-scala: says it found nothing to look for" 'introduces no name this can look for'
holds "nothing-scala: and that this is not the same as carrying nothing" 'read its diff against 7.0'

# A diff that cannot be taken is reported, not answered. `git diff A...B` on branches with no merge
# base fails; it used to reach `grep` through a pipe, so the pipeline carried grep's status and the
# `fatal:` became "introduces no name" with exit 0. `pre-rename` in this repository is exactly this.
run_subject orphan
echo "branch-content-landed, a branch with no merge base:"
check "orphan: refuses to answer" "$status" "2"
holds "orphan: names what failed" 'cannot diff orphan against 7.0'
holds "orphan: passes git's own words through" 'no merge base'
lacks "orphan: does not answer the question it could not ask" 'introduces no name'

summarise
