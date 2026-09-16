#!/bin/sh
# Are the names a branch introduces reachable from the line, so that deleting its ref loses nothing.
#
# WHY THIS EXISTS. The other half of the same incident. A branch sat forgotten for twenty-four
# commits; while somebody was recovering it, a second session deleted the ref because a commit with
# a similar TITLE had landed. That time the content really was in and somebody had checked, but the
# sequence contains no check of its own: with a partial recovery, or a similar title belonging to
# different work, the ref goes and takes the only copy of the names with it.
#
# WHAT IT ASKS, WHICH IS NOT WHAT A TITLE ANSWERS. Not "did something like this land", which is what
# a reader comparing commit subjects is doing, and not "is this commit an ancestor", which a rebase
# makes false about work that landed. It asks whether each NAME the branch introduces exists in the
# line's tree. A name is the thing a later development reaches for, so a name that is nowhere is
# work that is nowhere, whatever the history looks like.
#
# WHAT IT IS NOT. It is not a proof that deleting is safe. A branch can introduce no new name and
# still carry a proof nobody else has, and a name can be present in a weaker form than the branch
# proved it in. It answers one question cheaply and says so; the expensive question is what the
# branch's diff says, and this is what tells you whether you have to read it.

set -eu

branch="${1:-}"
line="${2:-}"

if [ -z "$branch" ]; then
    echo "usage: $0 <branch> [line]" >&2
    exit 2
fi

if [ -z "$line" ]; then
    line=$(git rev-parse --abbrev-ref HEAD)
    case "$line" in
        [0-9]*.[0-9]*) ;;
        *)
            echo "branch-content-landed: $line is not a release line; name one, as in" >&2
            echo "  $0 $branch 7.0" >&2
            exit 2
            ;;
    esac
fi

for ref in "$branch" "$line"; do
    git rev-parse --verify --quiet "$ref" >/dev/null || {
        echo "branch-content-landed: no such ref: $ref" >&2
        exit 2
    }
done

# The names the branch adds, from the lines it adds and not from the files it touches: a file the
# branch merely edits contributes the declarations that were already there and every one of them
# would be found, which is how a check like this passes about work it has not looked at.
#
# A failed diff is reported and not answered. It used to reach `grep` through a pipe, so the
# pipeline carried grep's status and a `fatal:` on stderr became "introduces no name this can look
# for" with exit 0, which is an absent answer printed as a negative one. It is reachable on this
# repository today: `pre-rename` is an orphan and `7.0...pre-rename` has no merge base.
if ! diff_text=$(git diff "$line...$branch" -- '*.scala' 2>&1); then
    echo "branch-content-landed: cannot diff $branch against $line" >&2
    printf '%s\n' "$diff_text" | sed 's|^|  |' >&2
    echo "  for a branch with no merge base, read \`git diff $line $branch\` by hand: what that" >&2
    echo "  range means is a different question from the one this answers" >&2
    exit 2
fi
added=$(printf '%s\n' "$diff_text" | grep '^+' | grep -v '^+++' || true)

# Two shapes, because this repository publishes both: a Scala declaration, and the quoted name of a
# lemma, which is what a development actually exports and what the incident lost.
#
# Each shape reads the same lines. The two used to be `sed` calls grouped on one stdin, which is one
# reader too many: the first consumes the stream to EOF and the second is handed nothing, so the
# quoted shape had never matched a line since the day it was written. Chaining them as two `-e`
# expressions of one `sed` is the repair that suggests itself and is also wrong, because the first
# substitution replaces the pattern space with the bare name and the second then reads that instead
# of the diff line. Holding the input costs what the input weighs: 82 KB for the largest branch this
# repository has, measured on `verify-quotient`.
names=$(
    {
        printf '%s\n' "$added" |
            sed -n -E 's/^\+[[:space:]]*(private |final |lazy |implicit |override |case )*(def|val|var|object|class|trait|type|enum)[[:space:]]+([A-Za-z_][A-Za-z0-9_]*).*/\3/p'
        printf '%s\n' "$added" |
            sed -n -E 's/.*"([A-Z][A-Z0-9_]{3,})".*/\1/p'
    } | sort -u
)

if [ -z "$names" ]; then
    echo "branch-content-landed: $branch introduces no name this can look for"
    echo "  that is not the same as carrying nothing: read its diff against $line"
    exit 0
fi

total=0
missing=0
for name in $names; do
    total=$((total + 1))
    if ! git grep -q -w "$name" "$line" -- '*.scala' 2>/dev/null; then
        [ "$missing" -eq 0 ] && echo "$branch introduces names $line does not have:"
        echo "  $name"
        missing=$((missing + 1))
    fi
done

if [ "$missing" -eq 0 ]; then
    echo "branch-content-landed: all $total name(s) $branch introduces are present in $line"
    echo "  deleting the ref loses no name; it may still lose a proof, so read the diff if it matters"
    exit 0
fi

echo
echo "$missing of $total name(s) are not in $line: do not delete this ref"
exit 1
