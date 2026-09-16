#!/bin/sh
# Run `branches-behind.sh` against a repository built for the purpose, in both shapes it meets.
#
# WHY THIS EXISTS, AND IT IS NOT "THE SCRIPT SHOULD HAVE TESTS". The thing it guards is a defect
# no perturbation of the answer could have caught, because every one of them asked whether the
# script recognises the condition and none asked whether it runs where it is installed. The
# pipeline checkout `actions/checkout@v4` leaves holds ONE local branch, the line, and every other
# branch only as `refs/remotes/origin/<name>`; a development machine holds them all locally. Read
# as revisions, bare names work in the second shape and are fatal in the first, so five hand checks
# passed while the installed script exited 128 on the first push that met a second branch. The two
# shapes are therefore the fixture, and an assertion that holds in one of them proves nothing.
#
# It is also why the pipeline runs THIS and not only the report. The report on this repository is
# green because the remote carries a single branch: green for want of anything to look at, which is
# the same silence the script itself exists against, one floor down.
#
# WHAT IT DOES NOT COVER. The fixture is built by `git init` and `git fetch`, which is the ref
# layout `actions/checkout@v4` produces and not the action itself. A change in what that action
# leaves behind would pass here and break there, and the only instrument for that is a run in the
# pipeline.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/branches-behind.sh"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=branches-behind-test
. "$here/test-harness.sh"

failures=0

# The population the fixture answers about, and the answer each member is there to force:
#   7.0               the line
#   carries-work      one commit the line has no equivalent patch for   -> reported
#   carries-a-merge   the same, with a merge commit in the range        -> reported, with a count
#   already-landed    one commit cherry-picked onto the line            -> silent, by patch
#   pre-rename        carries work and is on the exemption list         -> silent, by exemption
# plus `refs/remotes/origin/HEAD`, whose short form is `origin` and which is not a branch.
#
# `carries-a-merge` is here for the count `git cherry` cannot give: it reads no merge commit at
# all, so a branch whose merges are the work would be reported as carrying one commit and the
# reader would infer the rest landed. The second figure comes from `git rev-list`, which is the
# call this repair had to guard, so a fixture without a merge in range would assert that the
# guarded call does not crash and never that it still counts.
build_origin() {
    git_q init -b 7.0 --bare "$work/origin.git"
    git_q init -b 7.0 "$work/seed"
    cd "$work/seed"
    git_q remote add origin "$work/origin.git"
    echo one > f.txt
    git_q add f.txt
    git_q commit -m one

    git_q checkout -b carries-work
    echo work > carried.txt
    git_q add carried.txt
    git_q commit -m "work the line will not have"

    git_q checkout 7.0
    git_q checkout -b pre-rename
    echo old > marker.txt
    git_q add marker.txt
    git_q commit -m "the history before the rename"

    git_q checkout 7.0
    git_q checkout -b already-landed
    echo landed > landed.txt
    git_q add landed.txt
    git_q commit -m "work that will land on the line"

    git_q checkout 7.0
    git_q cherry-pick already-landed

    git_q checkout -b carries-a-merge
    echo side > side.txt
    git_q add side.txt
    git_q commit -m "work on a branch that also merges the line"
    git_q checkout 7.0
    echo moved > f.txt
    git_q commit -am "the line moves on"
    git_q checkout carries-a-merge
    git_q merge --no-ff -m "merge the line into the branch" 7.0

    git_q checkout 7.0
    git_q push origin --all
    cd "$work"
}

# The shape `actions/checkout@v4` leaves: no local branch but the line, everything else a
# remote-tracking ref, and `origin/HEAD` present.
build_pipeline_shape() {
    cd "$work"
    rm -rf "$work/pipeline"
    git_q init -b 7.0 "$work/pipeline"
    cd "$work/pipeline"
    git_q remote add origin "$work/origin.git"
    git_q fetch --no-tags origin '+refs/heads/*:refs/remotes/origin/*'
    git_q remote set-head origin 7.0
    git_q checkout -B 7.0 refs/remotes/origin/7.0
}

# The shape a development machine has: the same branches, locally, tracking the same remote.
build_development_shape() {
    cd "$work"
    rm -rf "$work/development"
    git_q clone "$work/origin.git" "$work/development"
    cd "$work/development"
    for branch in carries-work carries-a-merge pre-rename already-landed; do
        git_q branch --track "$branch" "origin/$branch"
    done
    git_q checkout 7.0
}

run_subject() {
    status=0
    report=$(cd "$1" && GITHUB_ACTIONS=true sh "$subject" 7.0 2>&1) || status=$?
}

# The answers, asserted identically in both shapes. A tool that answers differently depending on
# where the same branches are recorded is the defect this file is about, so the assertions are one
# list run twice rather than two lists.
assert_report() {
    check "$1: exits 0, having warned and not failed" "$status" "0"
    holds "$1: names the branch that carries work" '^carries-work carries 1 non-merge commit'
    holds "$1: annotates it for the pipeline" '^::warning title=branch left behind::carries-work'
    holds "$1: counts the merge commits it did not read" \
        '^carries-a-merge carries 1 non-merge commit.*plus 1 merge commit(s) not examined'
    lacks "$1: silent about the branch whose patch landed" 'already-landed'
    lacks "$1: silent about the exempt branch" 'pre-rename'
    lacks "$1: nothing died on a ref it could not read" 'title=branch not examined'
    lacks "$1: no git error reached the output" '^fatal:'
}

build_origin

build_pipeline_shape
run_subject "$work/pipeline"
echo "branches-behind, pipeline shape (branches only as refs/remotes/origin/*):"
assert_report "pipeline"

build_development_shape
run_subject "$work/development"
echo "branches-behind, development shape (every branch local):"
assert_report "development"

# `refs/remotes/origin/HEAD` is not a branch and the tool used to examine one called `origin`,
# because the short form of that ref is `origin` and the filter looked for `HEAD`. The canonical
# shapes above point it at the line, where the phantom compares equal to the line and the wrong
# answer is silence: asserted there, this passes against the defect, which is how it was written
# the first time and measured afterwards. Pointed at a branch that carries work, which is what a
# repository whose default branch is not its release line looks like, the defect speaks: the
# phantom is reported as a branch called `origin`, and nobody can push to that.
#
# In the development shape rather than the pipeline one, because only there does the defective
# version reach this line at all: in the pipeline shape it is already dead of the other defect, and
# a case that cannot separate the two versions is not a check.
build_development_shape
cd "$work/development"
git_q remote set-head origin carries-work
run_subject "$work/development"
echo "branches-behind, origin/HEAD pointing at a branch rather than at the line:"
check "origin/HEAD: exits 0" "$status" "0"
lacks "origin/HEAD: reports no branch called origin" '^origin[ :]'
holds "origin/HEAD: still reports the branch itself" '^carries-work carries 1 non-merge commit'

# The exemption list is read in both directions, and the direction that goes stale is the one no
# ordinary run exercises: an exemption outlives the branch it excuses and keeps passing for ever.
# Deleting the branch from the pipeline shape is what makes that case reachable at all.
build_pipeline_shape
cd "$work/pipeline"
git_q update-ref -d refs/remotes/origin/pre-rename
run_subject "$work/pipeline"
echo "branches-behind, an exemption whose branch is gone:"
check "stale exemption: exits 0" "$status" "0"
holds "stale exemption: reports the excuse that excuses nothing" 'the exemption for pre-rename names a branch this repository no longer has'

summarise
