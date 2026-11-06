# 0068. The licence is the AGPLv3, so a network service built on this code owes its source too

- **Status:** accepted, supersedes [0050](0050-the-licence-stays-gplv3-for-now.md)
- **Date:** 2026-11-06

## Context

`docs/adr/0050` kept the GNU General Public License, version 3, and said in its own words that the
choice was provisional. The question came back on 2026-11-06 for a concrete reason: the author
wants the strongest licence that still lets the repository be published as open source and be
accepted by programmes that take only licences on the open-source lists, without leaving room for
the code to be taken and run with nothing coming back.

What the GPL leaves open is the network. Its obligations attach to **distribution**, so a party
that runs a modified copy as a service, and never hands a binary to anybody, owes nothing. For a
system whose natural use by others is behind an interface (a prover answering requests, the
`Notebook` served over HTTP), that is the main way the code would be used without the GPL ever
applying.

The licences that would forbid commercial use outright (non-commercial Creative Commons, the
Business Source License, PolyForm, the Commons Clause, the SSPL) are not open source, and the
programme that occasioned this record refuses them by name. They were not candidates.

## Decision

**The licence is the GNU Affero General Public License, version 3 or (at your option) any later
version, `AGPL-3.0-or-later`.** Decided by Angelo on 2026-11-06. It is the GPLv3 with one more
obligation, its section 13: whoever modifies the program and lets users interact with it over a
network must offer those users the corresponding source.

`LICENSE` holds the text as GitHub's licence API serves it, which is the copy GitHub's detection
recognises. `README.md` (badge and closing section) and the `licenses` setting in `build.sbt`,
which is what the published POMs carry, say the same.

## Consequences

**Relicensing needed one agreement, and it was given.** As `docs/adr/0050` foresaw, relicensing
needs every copyright holder; on 2026-11-06 every commit on `7.0` (906 of 906) has the author as
its author, so the author's decision is the whole of it.

**What is already published stays GPL.** `symbolum-core_3:7.0.1` and every other version
published before this record were granted under `GPL-3.0-or-later`, and a grant cannot be
withdrawn. The AGPL applies from the first release cut after this record.

**The dependencies allow it, checked against `build.sbt` on 2026-11-06 rather than assumed.** The
main scopes depend on `commons-math3` (Apache 2.0), `JTransforms` (BSD 2-Clause) and the Scala 3
compiler (Apache 2.0); the test scopes on ScalaTest and ScalaCheck (Apache 2.0, BSD 3-Clause). The
vendored material under `third-party/` is Apache 2.0. Each of these is compatible with the AGPLv3
in the same way it is with the GPLv3, which is how `docs/adr/0050`'s unchecked sentence about the
dependencies is answered here.

**The cost 0050 named grows a little.** A consumer that could live with the GPL because it never
distributes (a service) cannot live with the AGPL. That is the point of the change, and it is the
same trade-off 0050 recorded, moved one step further toward keeping derived work open.

**What a licence does not do, written down so nobody reads more into this record.** Copyleft
guarantees that modifications come back as source; it does not guarantee money. A commercial
licence offered beside the AGPL (dual licensing) is the usual way to get that, and it is open to
the author while the author is the only copyright holder. It is not decided here; an outside
contribution accepted without an agreement granting relicensing rights would close it.

## Alternatives rejected

**Staying on `GPL-3.0-or-later`.** Leaves the network case open, which is the case this record is
about.

**A source-available licence (BSL, PolyForm, Commons Clause, non-commercial terms).** Would forbid
the use the author wants to prevent, and is not open source: a repository under one is refused by
the programmes and indexes that take only open-source licences, and is read by consumers as
proprietary.
