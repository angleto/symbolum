#!/bin/sh
# Report every branch carrying work the release line does not, and say nothing when there is none.
#
# WHY THIS EXISTS. A branch left behind is signalled by nothing here. Not the pipeline, which runs
# on pushes to a release line and never looks at the others; not the tracker, because work that
# arrives without a card leaves no row; not `git status`, because a branch with no worktree appears
# nowhere. One branch sat twenty-four commits behind with two proved lemmas on it and surfaced only
# because somebody asked whether there was anything to merge.
#
# WHAT IT BUYS, AND IT IS NARROWER THAN IT LOOKS. Measured on this repository: a deleted ref costs
# an index and not the data until a `gc` runs, and the content of a branch removed that way was
# still reachable through `git fsck --unreachable`. So this does not buy recoverability, which the
# object store already gives. It buys a warning while the ref still has a NAME, because recovering
# by content takes three steps and the first two each return a confident wrong answer: `git
# patch-id` over the line says "not here" when a rebase has changed the hunk context, and
# `--unreachable` says the history is intact without saying which commit is yours.
#
# WHY IT COUNTS PATCH-EQUIVALENCE AND NOT ANCESTRY. `git branch --no-merged` lists a branch whose
# work was cherry-picked or rebased onto the line, because the original commit is not an ancestor.
# Those are exactly the branches somebody already rescued, so a check that merely listed would
# shout loudest about the cases that are fine, and an alarm that never falls silent stops being
# read. `git cherry` marks a commit `-` when the line already holds an equivalent patch and `+`
# when it does not, and the `+` count is what this reports. Measured on 2026-09-16, that is the
# difference between one branch and two: `verify-quotient` had two commits the line did not contain
# by ancestry and zero by patch, and reporting it would have been the first false alarm.
#
# ITS OWN LIMIT, STATED BECAUSE IT DECIDES WHEN THE ANSWER IS WRONG. Patch-equivalence is defeated
# by a rebase that changes the context of every hunk, so a branch whose work landed in a reworked
# form is reported here as carrying it. That is the safe direction -- a name to look at rather than
# a silence -- and it is the direction this cannot be made exact in, because "the same work" is not
# a relation git can decide.
#
# It warns and never fails. A branch left behind is somebody else's unlanded work, and a blocking
# gate on that condition stops the wrong person.

set -eu

# The line to compare against. Taken from the argument, or from the checked-out branch when that is
# a release line: a number written here would be a figure the repository already knows, and it
# would be wrong the day `7.1` opens.
line="${1:-}"
if [ -z "$line" ]; then
    line=$(git rev-parse --abbrev-ref HEAD)
    case "$line" in
        [0-9]*.[0-9]*) ;;
        *)
            echo "branches-behind: $line is not a release line; name one, as in" >&2
            echo "  $0 7.0" >&2
            exit 2
            ;;
    esac
fi

git rev-parse --verify --quiet "$line" >/dev/null || {
    echo "branches-behind: no such ref: $line" >&2
    exit 2
}

# Branches nothing will ever merge, each with the reason it is here rather than a bare name. An
# entry with no reason outlives whatever justified it; an entry for a branch that is gone is an
# excuse for nothing, and both are reported below.
exempt_reason() {
    case "$1" in
        pre-rename)
            echo "the history before the project was renamed, kept as a marker and never to be merged"
            ;;
        *)
            echo ""
            ;;
    esac
}
exempt_names="pre-rename"

# Every branch, local and remote, once. A remote branch and its local counterpart are one piece of
# work and reporting both would double every line.
branches=$(
    git for-each-ref --format='%(refname:short)' refs/heads refs/remotes |
        sed 's|^origin/||' |
        grep -v '^HEAD$' |
        grep -v "^$line\$" |
        sort -u
)

# A branch somebody has checked out is not a branch somebody has forgotten, and on this repository
# several sessions work at once, each in a checkout of its own. Without this the tool reports every
# peer's live work, and its own, which is the alarm that never falls silent in a second costume.
# In the pipeline this removes nothing, because the only checkout there is the line.
#
# What it therefore does not report: a branch sitting in a checkout nobody has touched for weeks,
# which is forgotten and looks busy. That is a question about checkouts rather than about refs, and
# a survey of the open checkouts is what answers it.
in_use=$(
    git worktree list --porcelain |
        sed -n 's|^branch refs/heads/||p' |
        sort -u
)

found=0
noted=0
for branch in $branches; do
    reason=$(exempt_reason "$branch")
    if [ -n "$reason" ]; then
        continue
    fi

    if echo "$in_use" | grep -qx "$branch"; then
        continue
    fi

    # `git cherry` prints one line per commit of the branch that the line does not already contain
    # as an equivalent patch, `+` for absent and `-` for present. It does **not** examine merge
    # commits at all, so the population it answers about is the non-merge commits and nothing else.
    # Both numbers are reported for that reason: on this repository `pre-rename` is 455 commits off
    # the line and `git cherry` prints 384, and the missing 71 are merges it never looked at rather
    # than commits it found equivalent. A reader given only the 384 infers an overlap that is zero.
    ahead=$(git cherry "$line" "$branch" 2>/dev/null | grep -c '^+' || true)
    merges=$(git rev-list --count --merges "$line..$branch")
    when=$(git log -1 --format=%cr "$branch")

    if [ "$ahead" -eq 0 ]; then
        # Silence here would be an absent answer reported as a negative one. Every non-merge commit
        # landed, and the merges were not read, so what can be said is that and not "nothing".
        if [ "$merges" -gt 0 ]; then
            echo "$branch: every non-merge commit is already in $line, and $merges merge commit(s) were not examined"
            noted=$((noted + 1))
        fi
        continue
    fi

    found=$((found + 1))
    message="$branch carries $ahead non-merge commit(s) that $line has no equivalent patch for"
    [ "$merges" -gt 0 ] && message="$message, plus $merges merge commit(s) not examined"
    message="$message, last touched $when"

    if [ -n "${GITHUB_ACTIONS:-}" ]; then
        echo "::warning title=branch left behind::$message"
    fi
    echo "$message"
done

# An exemption for a branch that no longer exists is an excuse for nothing and would keep passing
# for ever, so the list is read in both directions.
for name in $exempt_names; do
    if ! git rev-parse --verify --quiet "$name" >/dev/null &&
       ! git rev-parse --verify --quiet "origin/$name" >/dev/null; then
        message="the exemption for $name names a branch this repository no longer has"
        if [ -n "${GITHUB_ACTIONS:-}" ]; then
            echo "::warning title=stale exemption::$message"
        fi
        echo "$message"
        found=$((found + 1))
    fi
done

if [ "$found" -eq 0 ]; then
    if [ "$noted" -gt 0 ]; then
        # Not "nothing". Something was not looked at, and saying nothing here would turn an absent
        # answer into a negative one, which is the whole species of defect this repository keeps
        # apart everywhere else.
        echo "branches-behind: nothing carries work $line does not, except what is noted above"
    else
        echo "branches-behind: nothing carries work $line does not"
    fi
fi

# Always. See the note at the top about whom a blocking gate would stop.
exit 0
