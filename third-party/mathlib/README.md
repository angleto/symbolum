# Mathlib, vendored

**EXCERPT — for anyone scanning the index:**
What of Mathlib is in this repository, where it came from, under what licence, and why it is a
copy rather than a path to somebody's checkout. It is the attribution notice for those copies and
nothing else: what they are *for* is tracks R and L of
[../../docs/evaluation.md](../../docs/evaluation.md), and what reads them is `RingCorpusSpec` and
`LinarithCorpusSpec` in `modules/tactics`.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## What is here

| | |
|---|---|
| `MathlibTest/Tactic/Ring/Ring.lean` | the test file for Mathlib's `ring` tactic, 303 lines, unmodified |
| `MathlibTest/Tactic/Linarith/Basic.lean` | the test file for Mathlib's `linarith` tactic, 842 lines, unmodified |
| `LICENSE` | Mathlib's licence, the unmodified Apache License 2.0 |

## Where it came from

| | |
|---|---|
| Project | [mathlib4](https://github.com/leanprover-community/mathlib4) |
| Commit | `520045ab14e26149ee970e2e617ca04b09bde5d6`, 2026-07-23 |
| Upstream paths | kept as they are upstream, so the origin is readable from the path |
| `Ring.lean`, SHA-256 | `6a8b156f26eb2137b130f8f5befe0cd4206cffd284583cd2afe52cefe333b86e` |
| `Basic.lean`, SHA-256 | `bec8beba78d1f52f3f19287f6bf01a5a72d278aa32bc83de5ce1cbeacca3d082` |
| `LICENSE`, SHA-256 | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |

## Licence and attribution

Mathlib is copyright The mathlib Community and is released under the Apache License, Version 2.0,
whose text is in `LICENSE` beside this file. This repository is under the GNU GPL v3, which Apache
2.0 material may be combined into; the combination is under the GPL and the Apache terms continue
to govern this directory. Nothing here is relicensed and nothing here has been changed: all three
files are byte-identical to upstream, which is what the hashes above are for.

Neither file carries a per-file copyright header, unlike most of Mathlib; the project's `LICENSE`
governs both. The canonical citation, from Mathlib's own `CITATION.md`, is: The mathlib Community,
*The Lean Mathematical Library*, CPP 2020, https://doi.org/10.1145/3372885.3373824.

## Why a copy and not a path

Because the alternative fails a rule this project holds: a test may not depend on ambient state,
and a suite that reads `~/…/mathlib/MathlibTest/…` passes or fails according to whether an
unrelated project happens to be checked out on the machine. That is not a benchmark, it is a
coincidence.

There is a second reason, and it is the one that matters more. A benchmark stops measuring the
moment somebody transcribes it: whoever copies the examples across chooses which ones to carry and
how to write them, and both choices flatter the system under measurement. Reading upstream's own
file means the corpus is upstream's, the selection rule is in code where it can be read and
argued with, and every count in track R is produced rather than typed. Freezing that file at a
named commit is what makes the counts reproducible; it is not laziness about updating it.

## Rules for this directory

- Nothing here is compiled, and nothing in `modules/` may import from it. It is data.
- Nothing here is edited. A change upstream is a new copy at a new commit, with the hashes and
  the counts in track R re-measured in the same change.
- Adding another vendored file means another entry in the tables above, with its hash.
