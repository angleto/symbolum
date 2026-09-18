#!/bin/sh
# Every unqualified scaladoc query in the generated documentation, and whether it resolved inside
# the entity whose docstring writes it.
#
# WHAT QUESTION THIS IS. The gate in `.github/workflows/ci.yml` greps the doc log for
# `No DRI found`, which scaladoc emits when it CANNOT resolve a `[[query]]`. A query that resolves
# to a DIFFERENT entity than the author meant emits nothing at all: the link works, the page
# exists, and it points somewhere else. `[[Undecided]]` written where some other `Undecided` is in
# scope is the shape, and this repository has four entities by that name.
#
# WHAT THE ANSWER TURNED OUT TO BE, and it is the reason to read this header before trusting a
# green run. At `423c12f` on 2026-09-18, over a `sbt clean doc` of eleven modules: 912 unqualified
# queries on 550 pages, of which 656 resolved to the writer's own entity, 25 to a member it
# inherits, 231 to a top-level entity of the module, and ZERO anywhere else. Not zero by luck.
# Scaladoc 3.3.5 resolves a query in the lexical and inheritance scope of the entity that writes
# it and NOWHERE ELSE, so a query either lands in that scope or fails loudly, and the case this
# file was written to catch is one the tool does not produce.
#
# THAT IS MEASURED AND NOT REASONED, because it decides what this file is for. `[[Problem]]` was
# put in a docstring of `sat/Resolution.scala`, whose `Cnf.Problem` is in scope for the COMPILER
# through `import Cnf.*`. Scaladoc answered `No DRI found`, not a link to `Cnf.Problem`. The
# import was then made explicit, `import Cnf.Problem` beside the wildcard, and the answer was the
# same: `No DRI found`. Scaladoc does not consult imports at all.
#
# SO WHAT THIS IS. Not a hunt through the prose for bad links; a gate on the assumption the
# paragraph above rests on. It goes red when an unqualified query resolves outside its writer's
# scope, which today means: a scaladoc whose resolution rules have changed, or a module that has
# grown a second package repeating a top-level name. Either of those makes the argument above
# stop holding, and the repair is to redo the measurement rather than to qualify a link. Written
# down here because a conclusion about an external tool at a version is the kind that goes stale
# without anything failing.
#
# THE RULE IT ENFORCES. An unqualified `[[Q]]` must resolve to something the entity writing it
# already has: its own member, a member it inherits, a name nested inside it, or a top-level entity
# of the module, which an unqualified name may always denote and which no sibling can shadow.
# Anything else is written from one entity and lands inside another, and the repair would be the
# one `CLAUDE.md` prescribes: qualify it from the top-level entity, `[[Cnf.Problem]]` rather than
# `[[Problem]]`.
#
# The fourth of those is an assumption and was measured rather than assumed: at `423c12f` no
# top-level name occurs in two packages of one module, the pairs that look like it being a class
# and its companion object in the same package, which scaladoc tells apart by namespace. A module
# that grew a second package with a repeated top-level name would make that bucket, 231 of the 912
# on that tree, stop being safe, and this file is what would say so.
#
# WHAT STAYS UNWATCHED, which is where the remaining defect lives. Intent. A query whose writer's
# own scope holds the name, written by an author who meant another entity's, resolves correctly by
# every rule here and lands on the wrong page; so does a QUALIFIED query naming the wrong path.
# Neither is decidable from outside, because the intention is written nowhere, and nothing here
# pretends otherwise.
#
# And scaladoc publishes neither private members nor links into them, so a query whose writer or
# whose target is private renders as plain text and never becomes an anchor: 912 of the
# repository's 1528 unqualified query sites reach this instrument at `423c12f`, about six in ten.
#
# THE CENSUS OVER THE SOURCES was the alternative and is not what landed, and the measurement is
# why. Counting, per site, how many entities of the module carry that name flags 217 sites reading
# the sources and 122 reading what scaladoc published. Reading them shows what the criterion is
# counting: `[[normalisation]]` in `Arithmetic` resolves to `Arithmetic.normalisation` and is
# flagged because `Polynomial` and `Semiring` have one too. Qualifying those 122 would add a
# prefix to a link that already lands where its author meant, which is noise rather than repair.
#
# WHY IT REFUSES AN EMPTY READING. A census with nothing to read is green, which is how a check
# like this passes for free; the doc task is cached, so an incremental `sbt doc` documents only
# what recompiled and a clean answer over two modules is an answer about two modules. So it
# prints the count it read and fails when there is nothing there, and the caller runs it after
# `sbt clean doc` rather than after `sbt doc`.
#
# Usage:
#   sh tools/scaladoc-scope.sh [ROOT]
#
# Exit codes: 0 when every unqualified query resolved in scope, 1 when one did not or when there
# was nothing to read.

set -eu

root=${1:-.}
api_glob='target/scala-3.3.5/api'

# `[ ... ] && continue` would be an AND-OR list whose status is the test's, and whether `set -e`
# ends the loop on it is a reading of the standard rather than a fact. Spelled as an `if`.
report=$(
  for api in "$root"/modules/*/"$api_glob"; do
    [ -d "$api" ] || continue
    find "$api" -name '*.html' ! -name 'index.html' -print
  done | while read -r page; do
    # A package page re-renders the brief of every member, so every link in a member's own
    # docstring appears there a second time and relative to the package. Reading it would count
    # each site twice and call every one of them off-scope.
    if [ -d "${page%.html}" ]; then continue; fi
    here=$(basename "$page" .html)
    here=${here%%\$\$*}
    here=${here%\$}
    awk -v page="$page" -v here="$here" '
      function tophtml(h,   b, n) {
        n = split(h, b, "/"); h = b[n]
        sub(/\.html$/, "", h)
        sub(/\$\$.*$/, "", h)
        sub(/\$$/, "", h)
        return h
      }
      NR == FNR {
        # Pass one: the fragment id of every member this page lists, its own and the ones it
        # inherits. An inherited member is listed here under the DECLARING class page, which is
        # what makes the fragment rather than the file the thing to compare.
        s = $0
        while (match(s, /<a href="[^"]*#[^"]*"[^>]*class="documentableName/)) {
          tok = substr(s, RSTART, RLENGTH)
          s = substr(s, RSTART + RLENGTH)
          sub(/^<a href="/, "", tok)
          sub(/".*$/, "", tok)
          sub(/^[^#]*#/, "", tok)
          member[tok] = 1
        }
        next
      }
      {
        s = $0
        while (match(s, /<div[^>]*>|<\/div>|<a href="[^"]*"[^>]*>[^<]*<\/a>/)) {
          tok = substr(s, RSTART, RLENGTH)
          s = substr(s, RSTART + RLENGTH)
          if (tok ~ /^<\/div>/) { if (depth > 0) depth-- ; continue }
          if (tok ~ /^<div/) {
            if (depth > 0) depth++
            else if (tok ~ /class="doc"/ || tok ~ /class="documentableBrief doc"/) depth = 1
            continue
          }
          if (depth == 0) continue
          href = tok; sub(/^<a href="/, "", href); sub(/".*$/, "", href)
          text = tok; sub(/^[^>]*>/, "", text); sub(/<\/a>$/, "", text)
          if (href ~ /^http/ || href ~ /^#/ || href !~ /\.html/) continue
          # A qualified query renders with the dots the author wrote, so a simple identifier is
          # exactly the unqualified case and is the whole population of this question.
          if (text !~ /^[A-Za-z_$][A-Za-z0-9_$]*$/) continue
          read++
          frag = ""; file = href
          if (href ~ /#/) { frag = href; sub(/^[^#]*#/, "", frag); sub(/#.*$/, "", file) }
          if (tophtml(file) == here) next_ok = 1
          else if (frag != "" && (frag in member)) next_ok = 1
          else if (frag == "" && file !~ /\$\$/) next_ok = 1
          else next_ok = 0
          if (!next_ok) printf "OFF\t%s\t%s\t%s\n", page, text, href
        }
      }
      END { printf "READ\t%d\n", read + 0 }
    ' "$page" "$page"
  done
)

found=$(printf '%s\n' "$report" | awk -F'\t' '$1 == "READ" { n += $2 } END { print n + 0 }')
pages=$(printf '%s\n' "$report" | grep -c '^READ' || true)
offs=$(printf '%s\n' "$report" | grep '^OFF' || true)

if [ "$found" -eq 0 ]; then
  echo "scaladoc-scope: read no query at all over $pages page(s), which is not an answer." >&2
  echo "scaladoc-scope: run 'sbt clean doc' first; an incremental doc task documents only what" >&2
  echo "scaladoc-scope: recompiled, and a clean report over two modules is about two modules." >&2
  exit 1
fi

if [ -n "$offs" ]; then
  echo "scaladoc-scope: an unqualified [[query]] resolved outside the entity that writes it."
  echo "scaladoc-scope: qualify it from the top-level entity of its own file."
  printf '%s\n' "$offs" | while IFS="$(printf '\t')" read -r _ page text href; do
    echo "  on $page: [[$text]] resolved to $href"
  done
  exit 1
fi

echo "scaladoc-scope: $found unqualified quer(ies) over $pages page(s), every one in scope."
