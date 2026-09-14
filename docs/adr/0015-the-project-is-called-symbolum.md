# 0015. The project is called Symbolum

- **Status:** accepted
- **Date:** 2026-09-14

## Context

**There is already a Symbolica.** `symbolica.io`, a crate on crates.io, and
`github.com/symbolica-dev/symbolica`: a high-performance computer algebra system for Rust and
Python, used at CERN, at ETH Zurich and at KIT. It is in this domain, it is one letter away, and it
is the better-known of the two by every measure there is. Somebody looking for one finds the other,
and a reader who meets `symbolicas` beside it concludes a fork or a typo. Neither conclusion is
recoverable by explaining afterwards.

The second reason is smaller and would not have been enough on its own: the name announces the
algebra and says nothing about the half that checks. This repository is a computer algebra system
**and** a proof assistant, and the relation between the two is the design rather than a feature of
it.

**What made it a decision now rather than later is that the cost is measurable and it only grows.**
Measured on 2026-09-10: `gh api user/packages?package_type=maven` answers `[]`, so nothing has ever
been published from here; on Maven Central under `io.github.angleto` there is only `whatsappweb4j`.
No consumer anywhere resolves a coordinate of this project from a registry. The repository is
private, with no fork, no star and no watcher. The only external consumer is a sibling checkout on
this machine, and it is reached by a classpath the build exports rather than by a coordinate.

Every one of those facts is temporary. A rename after the first publication is a rename with a
deprecation period attached.

## Decision

**The project is Symbolum.**

In Latin *symbolum* is the broken token: two parties keep a half each, and the token authenticates
by the halves being made to match. That is `docs/adr/0003` said in one word. The algebra half
proposes, the kernel checks, nothing is believed because of where it came from, and the two either
fit or they do not.

In ecclesiastical Latin *symbolum* is the **Creed**: the exact list of what one is asked to
believe, recited in full because a list of that kind is worth nothing when it is approximate. That
is the section of `CLAUDE.md` called "the trusted base, exactly", which names three items and
counts the axioms under each.

A word that means both of those, for a repository that is both of those, was not a shortlist. No
software collision was found for it.

**Reverse-DNS everywhere.** The organization is `garden.xeno`, the artifacts are
`symbolum-<module>`, and the packages are `garden.xeno.symbolum.*` under a source path that matches.
The domain `symbolum.xeno.garden` exists to justify the group identifier and to be the `homepage`
in the published metadata. There is no site and no page behind it, and publication stays where it
is.

**The version is 7.0.0**, on branch `7.0`, tagged `7.0.0`, neither carrying a `v`.

**The history is one orphan commit.** What preceded the rename is not carried forward.

**And one rule governs the whole rename, in this repository and in every other place the name
appears: the name changes where it points at the project, not where it dates a fact.** A record
saying "symbolicas at `a0944ea` on `v6.0`, frozen on 2026-09-07" is a record of what was true then,
and rewriting it makes it false. That covers dated notes, closed work items, verbatim quotations,
commit messages, archived copies of a failed attempt, and session transcripts.

## Consequences

**Every hash cited outside this repository stops being reachable, which is not the same as stopping
to answer, and the difference is the part worth writing down.** `a0944ea`, `aac0893`, `6a46a1b`,
`1c5f8c1`, `bb4c11b`, `be6f297`, `3649f3a`, `45007e2`, and the commits `collatz` cites in its own
source, name objects no branch and no tag can reach any more, here or on the server.

They were all still answering minutes after the old branches were deleted. Eleven were put to
`gh api repos/angleto/symbolum/commits/<sha>` on 2026-09-14, immediately after, and eleven came
back with a full commit: an unreachable object survives until something collects it, and neither
collection is on a schedule anybody here controls. So the citations in the records elsewhere will
stop working at a moment nobody chooses and without announcing it, which is worse than if they had
stopped at once. **Do not test one and conclude the rest are fine.**

The records that cite them stay readable as prose and are unverifiable as citations from now,
whatever the server still answers. That is the price of the orphan branch, and it is paid rather
than worked around: the alternative was carrying 455 commits of a project under a name it no longer
has, which is the thing the rename exists to stop.

**5 and 6 were never released.** The only tag this repository has ever carried is `v4.0.0`, 358
commits back, while `v5.0` and `v6.0` were written as lines and never tagged. Starting at 7.0.0
does not claim two releases nobody made: it takes the first number the two existing lines leave
free, so that the branch numbering and the tag numbering stop contradicting each other.

**The local directory and everything indexed by its path move together.** The session memory of the
assistant working here is keyed by the absolute path; the consumer's `certify.sh` derives this
project's location from a sibling path; `.bsp` and every `target/` hold absolute paths and are
discarded. None of that is automatic and none of it is announced by a failure at the time.

**The external consumer is `collatz`, and nothing in this build would have said so.** Files under
`code/symbolum/` import the packages and compile against the classpath `sbt export
theories/fullClasspath` prints. A rename of the packages breaks them, and it breaks them silently
until somebody runs `certify.sh`. So the consumer is repaired and run green **before** the history
is reset, because a consumer found broken afterwards has nothing to return to.

**Nothing about the trusted base moves.** The axiom count, the module graph and every statement of
the mathematics are what they were. A rename is not a mathematical change, and if one of the counts
in `docs/` moves during it, that is a defect in the rename and not a consequence of it.

## Alternatives rejected

**Keeping `symbolicas`.** The collision is the reason and it does not decay; it gets worse the
moment anything is published under the name. Every fact in the Context section that makes the
rename cheap today is a fact with an expiry date.

**Symbolon.** Greek for the same broken token, and the better word for the idea. There is an arXiv
paper from 2026 using it for a system doing symbolic execution, which is close enough in the
neighbourhood to reproduce the problem being solved.

**Symbolicum.** Keeps the stem and therefore keeps the collision: a reader who confuses
`symbolicas` with `symbolica` confuses `symbolicum` with it too.

**Symbola.** Douros's Unicode font, which every mathematician who has ever hunted a missing glyph
has installed. The name is taken in exactly the audience this project has.

**Symbolicon.** Symbolicons exists, and the ending pulls the reading towards "icon", which is a
word about pictures.

**symbolic-kernel.** Unambiguous and unfindable. It describes a component rather than naming a
project, and half of what is here is not a kernel.
