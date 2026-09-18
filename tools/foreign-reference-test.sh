#!/bin/sh
# Run `tools/foreign-reference.sh` against repositories built for the purpose, one per answer it
# can give, and against a stubbed git for the one answer only a broken instrument produces.
#
# WHY A FIXTURE AND NOT THIS REPOSITORY. The subject's own tree is clean and is meant to stay that
# way, so pointed at it the subject has exactly one answer and a version of it that had lost the
# ability to find anything would pass. The case that matters is the one this repository must never
# contain, so it has to be built somewhere else.
#
# WHY THE NEAR MISSES ARE A CASE OF THEIR OWN. A check that only ever sees its own defect passes by
# being blind, and the opposite failure is as bad: a shape one notch wider flags a charset, a
# digest and a standards number, all of which this repository writes. The four tokens in the second
# case are the ones measured on the real tree on 2026-09-18, and a subject that reported any of
# them would be red on a tree with nothing wrong with it.
#
# WHY A STUBBED GIT. The last case is the defect the subject exists because of: a pattern that has
# stopped matching reports a clean tree in the same words as a clean tree. Nothing inside the
# subject can be asked to demonstrate that, because the engine it would have to break is git's own,
# so a stub takes git's place on the PATH and answers the control's invocation with nothing while
# leaving every other invocation to the real thing. The assertion is that the subject exits 2 and
# says it did not read, rather than exiting 0 and saying the tree is clean.
#
# WHAT IT DOES NOT COVER. Whether git's `-w` means what it meant on 2026-09-18, which is a property
# of the tool and travels with its version; the first case is what would go red if it changed.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
subject="$here/foreign-reference.sh"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

harness_name=foreign-reference-test
. "$here/test-harness.sh"

failures=0

# Assembled rather than written, for the reason the subject's own pattern is: a literal specimen in
# a tracked file of this repository would be a finding in this repository, and this file is tracked.
token="XYZ-$(printf '%02d' 7)"

run() {
    out=$(sh "$subject" "$1" 2>&1)
    rc=$?
    report="$out"
    return $rc
}

# ONE: a tracked file citing a numbered clause of a document that is not here.
mkdir -p "$work/cited"
cd "$work/cited"
git_q init
printf 'The bound is what it is for the reason %s gives.\n' "$token" > note.md
git_q add note.md
git_q commit -m "a note"

echo "a tracked file carrying the citation"
set +e
run "$work/cited"
rc=$?
set -e
check "  exits 1" "$rc" "1"
holds "  names the file and line" "note.md:1:"
holds "  prints the token" "$token"
holds "  says what to do instead" "prose"

# TWO: the four tokens the real tree carries that a looser shape would flag. Nothing here is a
# citation, and a subject that reported one of them would be red on a clean repository.
mkdir -p "$work/nearmiss"
cd "$work/nearmiss"
git_q init
{
    printf 'The source is UTF-8 throughout.\n'
    printf 'The digest is SHA-256.\n'
    printf 'It follows CR-2003 in the numbering.\n'
    printf 'Licensed GPL-3 or later.\n'
} > prose.md
git_q add prose.md
git_q commit -m "prose with numbers in it"

echo
echo "a tracked file carrying the four near misses"
set +e
run "$work/nearmiss"
rc=$?
set -e
check "  exits 0" "$rc" "0"
holds "  reports the file count it read" "1 tracked file"
lacks "  flags none of them" "UTF-8\|SHA-256\|CR-2003\|GPL-3"

# THREE: the same citation, untracked. The subject reads the tracked set, so this is clean, and the
# pair with case one is what says so: the same bytes in the same directory, one answer each way.
mkdir -p "$work/untracked"
cd "$work/untracked"
git_q init
printf 'kept out of the tree\n' > tracked.md
git_q add tracked.md
git_q commit -m "one tracked file"
printf 'The bound is what it is for the reason %s gives.\n' "$token" > loose.md

echo
echo "the same citation in a file nobody tracked"
set +e
run "$work/untracked"
rc=$?
set -e
check "  exits 0" "$rc" "0"
lacks "  does not name the untracked file" "loose.md"

# FOUR: a repository with nothing tracked in it. The walk reaches no file, so an absence here says
# nothing about anything, and the subject must not spell it the way it spells a clean tree.
mkdir -p "$work/empty"
cd "$work/empty"
git_q init

echo
echo "a repository with nothing tracked in it"
set +e
run "$work/empty"
rc=$?
set -e
check "  exits 2" "$rc" "2"
holds "  says the instrument did not read" "did not read"
holds "  names the control that failed, which is the walk" "reached no file"
lacks "  does not call it clean" "no unresolvable reference"

# FIVE: not a repository at all.
mkdir -p "$work/plain"
echo
echo "a directory that is not a repository"
set +e
run "$work/plain"
rc=$?
set -e
check "  exits 2" "$rc" "2"
holds "  says so" "not a git repository"

# SIX: the instrument's own blindness, which is the failure this whole tool exists because of. The
# stub answers the control's `grep --no-index` with nothing and hands every other invocation to the
# real git, so the subject's pattern is intact and only its ability to demonstrate that is gone.
mkdir -p "$work/bin"
real_git=$(command -v git)
cat > "$work/bin/git" <<STUB
#!/bin/sh
# Blind for exactly the control's invocation, faithful for everything else.
for arg in "\$@"; do
    if [ "\$arg" = "--no-index" ]; then
        exit 1
    fi
done
exec "$real_git" "\$@"
STUB
chmod +x "$work/bin/git"

echo
echo "a git whose pattern matches nothing"
set +e
out=$(PATH="$work/bin:$PATH" sh "$subject" "$work/cited" 2>&1)
rc=$?
set -e
report="$out"
check "  exits 2" "$rc" "2"
holds "  says the instrument did not read" "did not read"
holds "  names the control that failed, which is the pattern" "expected to match"
holds "  says no conclusion follows" "no conclusion"
lacks "  does not report the finding it can no longer make" "note.md:1:"

summarise
