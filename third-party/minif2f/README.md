# miniF2F, vendored

**EXCERPT — for anyone scanning the index:**
Which part of miniF2F is in this repository, where it came from, under what licence, and why the
Lean 3 half rather than one of the Lean 4 ports. It is the attribution notice for those copies and
nothing else: what they are *for* is track M of [../../docs/evaluation.md](../../docs/evaluation.md),
and what reads them is `ReachSpec` in `modules/tactics`.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## What is here

| | |
|---|---|
| `lean/src/test.lean` | the 244 test statements, 2538 lines, unmodified |
| `lean/src/valid.lean` | the 244 validation statements, 2380 lines, unmodified |
| `LICENSE` | the Apache License 2.0, and see the paragraph below about where it came from |

## Where it came from

| | |
|---|---|
| Project | [miniF2F](https://github.com/openai/miniF2F) |
| Commit | `4e433ff5cadff23f9911a2bb5bbab2d351ce5554`, 2022-06-02, which is the head of `main` |
| Upstream paths | kept as they are upstream, so the origin is readable from the path |
| `test.lean`, SHA-256 | `fe8830147623fffbb7f55f878de363fdb2f9738c269b68ab11b31f6e3d59c5fb` |
| `valid.lean`, SHA-256 | `46a8162d75ca3350eaf7843c2af16eb90c15553c70df34e8d2f636547ca26028` |
| `LICENSE`, SHA-256 | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |

## Licence and attribution

Both Lean files carry the header *Copyright (c) 2021 OpenAI. All rights reserved. Released under
Apache 2.0 license as described in the file LICENSE*, and the project README says the same in
prose: **the `lean` folder is released under the Apache License**, the other language folders under
other licences, which is why only this folder is here.

**The `LICENSE` beside this file is not a copy of an upstream file, and that is worth stating
plainly rather than leaving to be discovered.** The miniF2F repository ships no `LICENSE` at any
path: its per-file headers point at one that is not in the tree. What is here is the canonical
Apache License 2.0 text, and it is byte-identical to `../mathlib/LICENSE`, which *was* copied from
upstream — the two hashes above and in that notice are the same string, and that is the check.

This repository is under the GNU GPL v3, which Apache 2.0 material may be combined into; the
combination is under the GPL and the Apache terms continue to govern this directory. Nothing here is
relicensed and neither Lean file has been changed.

The citation, from the paper the benchmark is described in: Kunhao Zheng, Jesse Michael Han and
Stanislas Polu, *MiniF2F: a cross-system benchmark for formal Olympiad-level mathematics*, ICLR
2022, https://arxiv.org/abs/2109.00110.

## Why the Lean 3 half and not a Lean 4 port

The reason is that the statements are what is being measured and the tactic proofs are not, and the
statements barely moved between the two.

There are two Lean 4 ports. `yangky11/miniF2F-lean4` splits the benchmark into 488 one-theorem
files and its own README says it is not maintained regularly; `facebookresearch/miniF2F` is a fork
that is still Lean 3 in the `lean` folder and adds informal statements beside it. Neither is the
repository the paper names.

What decided it is `LeanCorpus.declarations`, which cuts a file into declarations by Lean's layout
convention: a keyword at column zero, then the indented lines under it. Lean 3 writes a proof as
`begin … end` with `begin` at column **zero**, so the cutter stops at exactly the right place and
every declaration here arrives with its statement whole and its proof empty. That is the shape this
measurement wants — a statement to read and nothing to compare a tactic against — and it needed no
change to the cutter to get it. A Lean 4 port would have needed 488 files read instead of two, to
answer the same question about the same mathematics.

## Why a copy and not a path

The same reason the notice beside `../mathlib` gives: a benchmark that lives at somebody's checkout
is a benchmark whose number cannot be reproduced later, and transcribing one by hand is where a
benchmark stops measuring, because whoever copies the examples chooses which to carry and how to
write them, and both choices flatter the system being measured.
