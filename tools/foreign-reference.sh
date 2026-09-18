#!/bin/sh
# Every identifier-shaped cross-reference in a tracked file must resolve inside this repository.
#
# WHAT IT LOOKS FOR, described rather than spelled, because a literal specimen in this file would
# be found by this file. Two to four capitals, a hyphen, exactly two digits, standing as a whole
# word. That shape is how a numbered clause of an external document is cited, and this repository
# has no such document: its own cross-references are `docs/adr/NNNN`, a lemma name, a spec name or
# a file path, and every one of those a reader can open from the checkout in front of them.
#
# WHY IT MATTERS, WHICH IS NOT TIDINESS. A reference a reader cannot resolve is worse than no
# reference at all: it reads as a citation, so the reader believes a justification exists and is
# written down somewhere, and stops looking for the argument in the text. The repair is never to
# add the missing document; it is to write the reason in prose, where it is checkable by the person
# reading the line it explains.
#
# WHY A SHAPE AND NOT A LIST. A list of the prefixes that are forbidden would have to be carried
# here, and it would then be the very thing a reader of this repository is not meant to have to
# resolve. The shape is a wider net and needs no list, and the width was measured rather than
# assumed: see the paragraph below.
#
# WHAT THE WIDTH COSTS, MEASURED ON THE TRACKED TREE AT 245df49 ON 2026-09-18. Zero matches, with
# the instrument's controls passing on the same run. Widening to one-to-four digits and two-to-five
# capitals, which is the nearest looser shape, brings back 32 lines and four distinct tokens:
# UTF-8 (21), SHA-256 (7), CR-2003 (3) and GPL-3 (1). None of those matches the shape this asks
# for: UTF-8 and GPL-3 have one digit, and SHA-256 and CR-2003 continue into a third digit, which
# the whole-word condition rejects. So there is no exemption list here, and that is a measurement
# rather than an omission. If one is ever needed, it is added with the token and the reason.
#
# WHY `-w` RATHER THAN `\b`, WHICH IS THE DEFECT THIS TOOL EXISTS BECAUSE OF. The first census of
# this class was written as `git grep -E` with `\b` word boundaries, and it answered zero over the
# whole repository. It was not zero. POSIX extended regular expressions have no `\b`, so the
# pattern matched nothing anywhere, and the run was indistinguishable from a clean tree. Measured
# here on 2026-09-18 against a six-line specimen holding one planted token: `-w -E` and `-P` with
# `\b` each return that one line, `-E` with `\b` returns nothing at all, and `-E` with no boundary
# at all returns three lines, two of them false. `-w -E` is what this runs, because it gives the
# same answer as the Perl engine and, unlike it, does not require git to have been built with
# PCRE: a git without it fails the invocation, which on a check whose whole job is to report an
# absence is the worst available failure.
#
# WHAT IT REFUSES TO DO, AND THIS IS THE POINT OF THE TWO CONTROLS. It never reports an absence it
# has not earned. Before it reports that the tree is clean it establishes twice that it can see:
# once that the pattern still matches a specimen it plants itself, and once that the walk over the
# tracked tree reaches at least one file. Either control failing exits 2 and says the instrument
# did not read, which is a different answer from a clean tree and must never be confused with one.
#
# WHAT IT DOES NOT COVER. Commit messages, which are not tracked files and which no check inside a
# repository can reach before they are written; and a reference that resolves nowhere but is not
# shaped like a numbered clause, which is a reading and not a grep.
#
#     sh tools/foreign-reference.sh [REPOSITORY]
#
# Exit 0: the instrument read and the tree is clean. Exit 1: at least one match, printed.
# Exit 2: usage, or the instrument could not be trusted to have read.

set -eu

root="${1:-}"

if [ -z "$root" ]; then
    root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
fi

if [ ! -d "$root" ]; then
    echo "foreign-reference: no such directory: $root" >&2
    exit 2
fi

if ! git -C "$root" rev-parse --git-dir >/dev/null 2>&1; then
    echo "foreign-reference: not a git repository: $root" >&2
    exit 2
fi

# Assembled rather than written, so that this file carries the shape and no instance of it. A
# literal here would be a match, and a tool that has to exempt its own source has a hole in it the
# width of whatever else gets written there.
capitals='[A-Z]{2,4}'
digits='[0-9]{2}'
pattern="$capitals-$digits"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

# CONTROL ONE: THE PATTERN STILL MATCHES. The specimen is written here and its token assembled at
# runtime for the same reason the pattern is: a planted specimen spelled out in this file would be
# a finding in this file. The lines around it are the four tokens the measurement above found on
# the real tree, so this control also holds the boundary condition that separates them.
specimen="$work/specimen.txt"
token="XYZ-$(printf '%02d' 7)"
{
    printf 'a charset named UTF-8\n'
    printf 'a digest named SHA-256\n'
    printf 'a standard named CR-2003\n'
    printf 'a licence named GPL-3\n'
    printf 'a clause cited as %s\n' "$token"
    printf 'a line with nothing of the kind\n'
} > "$specimen"

control_hits=$(cd "$work" && git grep --no-index -c -w -E "$pattern" -- specimen.txt || true)
if [ "$control_hits" != "specimen.txt:1" ]; then
    echo "foreign-reference: the instrument did not read." >&2
    echo "  the pattern was expected to match exactly the one planted line of the specimen" >&2
    echo "  and matched: ${control_hits:-nothing}" >&2
    echo "  no conclusion about $root follows from this run." >&2
    exit 2
fi

# CONTROL TWO: THE WALK REACHES THE TREE. The same command, the same pathspec, the same tracked
# set, asking for something whose answer cannot be zero in a repository with a file in it. Without
# it a pathspec that names nothing, a repository with an empty index or a checkout that is not
# where this thinks it is all report a clean tree in the same words as a clean tree.
reached=$(git -C "$root" grep -l -I -E '.' -- . 2>/dev/null | wc -l | tr -d ' ')
if [ "$reached" = "0" ]; then
    echo "foreign-reference: the instrument did not read." >&2
    echo "  the walk over the tracked tree of $root reached no file at all." >&2
    echo "  no conclusion about that tree follows from this run." >&2
    exit 2
fi

found=$(git -C "$root" grep -n -I -w -E "$pattern" -- . || true)

if [ -z "$found" ]; then
    echo "foreign-reference: $reached tracked file(s) read, no unresolvable reference"
    exit 0
fi

echo "foreign-reference: a reference nothing in this repository resolves" >&2
printf '%s\n' "$found" | sed 's|^|  |' >&2
echo >&2
echo "  Each of those cites a numbered clause of a document this repository does not contain," >&2
echo "  so a reader who follows it arrives nowhere. Write the reason in prose where the line" >&2
echo "  is, which is what the citation was standing in for, and delete the token." >&2
exit 1
