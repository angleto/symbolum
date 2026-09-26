# 0050. The licence stays GPLv3 for now, and the question is answered rather than left open

- **Status:** accepted
- **Date:** 2026-09-25

## Context

`LICENSE` is the GNU General Public License, version 3, and it has been since the first commit.
`README.md` shows it with a badge and states it in its closing section, and `build.sbt` publishes
it in the artifacts' metadata as `GPL-3.0-or-later`.

The question whether that is the right licence was raised twice before this record and answered
neither time. The first time, it was named as a trade-off to expose rather than to decide; the
second, it was the one item of a collection of ten that no agent could close, because the answer is
the author's. What made it worth asking again is that the library now has a consumer's coordinates:
`modules/core` is published as `garden.xeno:symbolum-core`, and a licence is the first thing a
project deciding whether to depend on it reads.

The trade-off, as it stood when the question was put:

- **The cost.** The proof assistants a reader compares this with are under permissive licences:
  Lean and Mathlib under Apache 2.0, Isabelle and HOL Light under BSD-style terms. A library under
  the GPL can be depended on only by software whose own licence is compatible with it, so for a
  closed or permissively licensed consumer it is an obstacle those projects do not have.
- **The reason it is chosen.** What is built on this code and distributed stays open under the same
  terms, which is what the GPL exists to guarantee and what a permissive licence gives away.

## Decision

**The licence stays the GNU General Public License, version 3.** Decided by Angelo on 2026-09-25,
in these words: *"per il momento scelgo la GPL3 poi vedrò se cambiare licenza"* (for now I choose
GPL3, and I will see later whether to change the licence).

Nothing in the repository changes with this record: `LICENSE`, the README's badge and section, and
the metadata in `build.sbt` already say it.

## Consequences

**The decision is provisional by its author's own statement, and that is part of it rather than a
weakness in it.** What this record removes is the open question, which is what had kept coming
back; it does not promise that the answer is final. A change of licence later is a new record that
supersedes this one, as `docs/adr/0004` is superseded rather than edited.

**What a later change would have to face, written down now because it is cheapest to know early.**
Relicensing needs the agreement of everyone who holds copyright in what is being relicensed. Today
that is the author alone, and the repository's history is the record of who wrote what; every
outside contribution accepted under the GPL makes a later change of licence need one more
agreement. The dependencies do not constrain the choice in either direction as far as this record
knows, and that is an unchecked statement rather than a measured one: nobody has audited their
licences against a permissive alternative, and a change would start there.

**Which GPL version, settled on 2026-09-26.** The published metadata says `GPL-3.0-or-later`,
which allows a recipient to use the terms of any later version of the GPL as well, while the
decision above was stated as "GPL3". The two are the same licence text and differ only in that
permission. When this record was accepted the difference was left open; the verification of the
card that asked for it put the question to the author, and the answer is `GPL-3.0-or-later`, as
`build.sbt` publishes it and as the POM of `symbolum-core_3:7.0.1` already granted it, which could
not be withdrawn for that version in any case. The README says "version 3 or later" accordingly.

## Alternatives rejected

**Apache 2.0, the licence of Lean and Mathlib.** It removes the adoption cost and gives up the
guarantee that what is built on this code stays open. Not chosen, for now.

**Leaving the question open until there is a consumer who asks.** That is what happened twice, and
it is the reason this record exists: an unanswered question costs a reading every time somebody
meets it, and an answer, even a provisional one, costs one record.
