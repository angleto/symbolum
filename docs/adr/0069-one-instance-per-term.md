# 0069. One instance per term, because a chain held 13.2 million applications spelling 1.68 million

- **Status:** accepted
- **Date:** 2026-11-09

## Context

Mycelium card `580c80ef` was opened on 2026-11-05. During the verification of card `25c7d137`, a
sampler on the forked test JVM of `tactics`, at its `-Xmx1024m`, read 966 MB while `ReachSpec`
ran. That sampler forced a collection with `jcmd GC.run` and then summed the occupancy `jstat`
reported. **That sum is not the live heap.** It includes whatever the suite allocated between the
collection and the read. Measured on 2026-11-09 in one run, the same forced collections read 463
to 495 MB in the GC log and 530 to 669 MB through `jstat`. Every figure below comes from the GC log
(`-Xlog:gc`), read at the occupancy after a full collection.

Measured that way on 2026-11-06 at `327ee472`, with a class histogram every 20 s, the live heap was:

- about 675 MB from `PropositionalRouteSpec` onwards;
- 700 to 744 MB in `ReachSpec`;
- 700 MB until the module ended.

The peaks are the problem. Over the whole module G1 ran eighteen `Pause Full (G1 Compaction
Pause)`, fourteen of them in `ReachSpec` between 18:10:01 and 18:10:53. Each was forced because the
heap was full: young collections left 1022 to 1023 MB of 1024. Each one recovered to about 730 MB,
and the module passed, 614 of 614. So it passed with no room left.

**The suites do not hold that heap. The chain does.** A probe built `Chain.standard` and then
every shared singleton `tactics` builds: `Arithmetic`, `Ring`, `Order`, `Linarith`, `Field`,
`Prove`, `Cost`, `Novelty`, `Propose`, `Family` and `Algebraic` `.standard`, `Library.of(chain)`
and `Cost.construct(chain)`. It read the used heap after `System.gc()`, at `-Xmx3g`:

| what | live after it |
|---|---|
| `Real.constructed` | 43 MB |
| `Chain.standard` | 663 MB |
| all the singletons above, on top | 670 MB |

The suspicion that some `*.standard` rebuilt the bottom of the chain a second time is refuted:
together they hold 7 MB.

What the chain is made of was a census. It walked, by identity, every theorem reachable from the
library's 1127 entries through `Derivation.premises`, which reaches 3 656 301 theorems. It counted
every term object reachable from their sequents and from the terms their derivation nodes carry.
The same objects were then counted as values:

| class | objects | distinct values | objects per value |
|---|---|---|---|
| `App` | 13 195 590 | 1 677 457 | 7.87 |
| `Const` | 2 871 266 | 752 | 3818 |
| `Abs` | 402 040 | 47 718 | 8.43 |
| `FVar` | 299 741 | 600 | 500 |
| `BVar` | 126 983 | 13 | 9768 |

The fork's histogram counted 13.4 million `App`, so the library reaches nearly all of them. At 24
bytes an object, the copies of `App` and `Const` were about 345 MB of a 620 MB chain. They are
copies for the reason `docs/adr/0058` gave for types. Nothing in the kernel shares a term once it
is built. Every rule builds its conclusion afresh, and every equation it builds carries a new `=`.

`docs/adr/0058` named this as what it did not reach: "hash-consing terms is the same idea at a
thousand times the table size, which makes a strong table a leak across chains and a weak one a new
mechanism in the trusted base; it is not decided here." This record decides it.

## Decision

**Every term has one instance per value, held weakly.** Each of `App`, `Abs`, `Const`, `FVar` and
`BVar` has a private constructor. Its companion's `private[kernel]` factory hands the new object to
`Interned`, in `Term.scala`, which returns the instance already in its table or inserts this one.

- **The table.** A `ConcurrentHashMap` keyed by a `WeakReference` that keeps its referent's hash.
- **Equality.** Two entries are equal when their referents are.
- **Insertion.** `putIfAbsent`, which is what makes a race on a new term safe, as it is for types.
- **Cleared entries.** A cleared entry is equal only to itself. The entries the collector clears are
  removed from a reference queue on the next construction. A lookup that finds an entry cleared
  between the hash and the read removes it and asks again.

**Equality stays structural**, so no rule, comparison or theorem can depend on which instance a
caller holds. A lookup costs one hash, which `App` and `Abs` already kept, and on a hit one shallow
comparison, since the children are interned already. `Rewrite.changed` and `Rewrite.idle` compare
sides by reference first, and they now find that reference more often. They were written to take a
reference match as the identity, so that changes what they skip and not what they conclude. The
census above counts the same 3 656 301 theorems after the change as before it.

**Weak rather than strong**, for the reason 0058 named. A strong table holds every term a process
ever spelt, for as long as the process lives, across every chain it builds. A property test drawing
random terms would grow it without bound. With weak entries, a term no theorem holds is collected
as it was before, and `TermInterningSpec` sees one go.

**`fromProduct` refuses, and that closes a route that existed before this change.** Scala 3
makes a case class's companion its `Mirror.ProductOf`, whose `fromProduct` calls the constructor
whatever the constructor's access is, and the compiler refuses a declared one that is narrower.
0058 found the same for `TyApp`. Before this change no companion declared it, so `App.fromProduct`
was not a member callable by name and did not compile from outside; the route was the derived
mirror, which any caller can summon. Measured at `0fa92517` from a package outside the kernel,
before this change, on 2026-11-09 and again at Scala 3.3.5 on 2026-11-10:

- `summon[Mirror.ProductOf[App]].fromProduct((p, x))`, with `p : bool`, built `p x`, which
  `Term.app` refuses with `NotAFunction`.
- `summon[Mirror.ProductOf[BVar]].fromProduct(Tuple1(3))` built a loose index, `?3`.
- `summon[Mirror.ProductOf[Abs]].fromProduct((bool, that))` built `\x:bool. ?3`, an abstraction
  that is not locally closed, which `Kernel.refl` refuses with `KernelInvariantViolation`.

This record said until 2026-11-10 that `App.fromProduct((p, x))` was the call that built, and it
did not compile at `0fa92517`: the independent verification of the card found it.

A theorem is not shown to come out of these. Producing one would need a rule that trusts its
argument's type, and every kernel rule is entitled to: "well-typed by construction" was false of
these three routes. So the `fromProduct` of all five term classes now refuses, with
`UnsupportedOperationException`. That includes `FVar`'s, even though a free variable is what
`Term.variable` builds for anyone, because one rule for all five is less to read than a rule and
an exception. Nothing in the repository called any of them. `TrustBoundarySpec` asks this from
outside the package, through the companion and through the derived `Mirror`.

**Each class has a table of its own**, so that the instance a lookup returns has the candidate's
class without a cast. A cast in the trusted base would be one more place where the type system is
not doing the checking.

**The trusted base bound goes from 1240 lines to 1300.** The four files were 1238 lines, two under
the bound, and the change is sixty-one lines with its comments, so they are 1299. It belongs inside
the count for the reason 0058 gave: a table that handed back the wrong instance for a key would
change what a term says. `DocumentationSpec` holds the bound and the documents that quote it.

**`ReachSpec` counts replayed steps without writing the proof.** Its last test counted the `s `
lines of `Proof.write` for each proved corpus statement, twice per statement. A proof that cites
the library is written with the library beneath it, so each call built the text and a table of
every term the proof reaches. In the run with only the interning landed, that one test took the
fork from about 480 MB live to a full heap and a compaction. `Proof.steps` is the same count
through the same walk `write` numbers its steps by. `DerivationSpec` holds it equal to the text's
count, through a citation as well. `Proof.scala` is outside the trusted base.

## Measured

The same probe as above, read after `System.gc()` at `-Xmx3g`:

| kernel | live after `Chain.standard` | after every singleton |
|---|---|---|
| as it was (`327ee472`, 2026-11-06) | 663 MB | 670 MB |
| one table for every term class (2026-11-09) | 439 MB | 441 MB |
| **one table per class, as landed (2026-11-09)** | **452 MB** | |

The census reads one object per value in every class: 1 677 457 `App`, 47 718 `Abs`, 752 `Const`,
600 `FVar` and 13 `BVar`. It counts the same 3 656 301 theorems as before the change. That census
was run on the single-table variant. The landed variant differs from it in which table an entry
lands in, not in which entries exist.

The tables' own cost is inside the 452. It was read off `jcmd GC.class_histogram` on the probe's
JVM after the chain was built:

| class | instances | MB |
|---|---|---|
| `Interned$Entry` | 1 736 916 | 69.5 |
| `ConcurrentHashMap$Node` | 1 830 175 | 58.6 |
| `ConcurrentHashMap$Node[]` | 54 | 17.7 |

That is about 146 MB in all. The map rows include the type table and the few other maps of the
process. The copies the tables removed were about 345 MB.

The chain's build time is not compared here. The three readings, 227 s, 140 s and 45 s, were
taken with the machine's load average between about 5 and over 100, and they say more about the
load than about the kernel.

**The forks, after.** The full suite on the landed tree was `tools/sbt test` with `-Xlog:gc` added
to the `theories` and `tactics` forks. It passed: 3071 tests, 0 failed, over 10 modules, which is
the 3064 of 2026-11-05 and the seven added here. The live heap was read from the GC log at the
forced full collections, one a minute:

| fork | live, highest | `G1 Compaction Pause` | highest occupancy after a young collection |
|---|---|---|---|
| `tactics`, 2026-11-06, kernel as it was | 744 MB | 18 | 1023 MB |
| `tactics`, 2026-11-09, as landed | 514 MB | **0** | 1002 MB |
| `theories`, 2026-11-09, as landed | 514 MB | **0** | |

The 1002 MB is in `NoveltySpec`, at 13:30:40. An occupancy after a young collection still holds
old-generation objects the concurrent cycle has not reached, so it is not the live heap. The
forced full collection at 13:30:22 read 514 MB, and G1 reclaimed the rest without a compaction.
`theories` was not measured by this criterion before the change. The figure the verification of
`25c7d137` gave for it, 884 MB, came from the `jstat` sum described at the top.

`TermInterningSpec`, in the kernel's tests, asserts identity (`eq`) in these cases:

- a term built twice;
- a term reached through `Term.eq`, through `Term.substitute` and through a beta step;
- a constant asked of a theory twice, and equality at a type;
- one term built on sixteen threads at once.

It also asserts that a term nothing holds is collected, and the four refusals.
`tools/verify/perturb-term-interning.sh` fires them, and on 2026-11-09 it read:

1. **Control: green.** `TermInterningSpec` and `TermPropertySpec` 17, `TrustBoundarySpec` 9.
2. **The table handing back the candidate:** red on all four identity tests and on the kept-hash
   property, `false was not equal to true`. The refusal stayed green, as it should.
3. **`App.fromProduct` building again:** red on the refusal inside the package and on the one in
   `TrustBoundarySpec` outside it, each in a run of its own, because sbt stops at the first red
   command.

The tool restored the bytes and verified the restore. The red of the refusal on the kernel as it
was is the measurement above: there, the same calls built the terms.

`TermPropertySpec` asserted that a term rebuilt by abstraction and beta is a *different* object,
so that its hash comparison could not pass by reference. That is now false by construction, and
the assertion is turned around: the table finds the existing instance only through the kept hash,
so a rebuilt node whose hash disagreed would come back as a second object. `eq` is now what
carries the property.

## What it does not reach

**The proof record.** A chain still keeps every intermediate theorem, 3.66 million of them, and
the derivation nodes beside them. This makes each of them smaller and does not make fewer of them.
0058's reasons for keeping the record stand.

**Traversals that rebuild what they do not change.** `Term.substitute`, `substituteTypes`, `open`
and `close` still construct every node they pass. The table now hands back the instance already
there, so what they waste is time, the allocation of a candidate and a lookup, and no longer
memory. 0058 measured sharing in the traversals at 51 MB on its own. That was before this change,
and it is not measured after it.

**The table's size.** It is bounded by the distinct terms alive at once, not by the terms ever
spelt, and each entry costs more than the `App` it points to. A workload whose terms are mostly
unique would pay for the table and gain nothing. The one workload measured, the chain, repeats an
application about eight times.

## Rejected

**Raising the fork's heap.** For the reasons 0058 and card `4222de0a` gave: the machine's free
memory during a coverage run, and a heap that grows with the chain buys one more link each time.

**A strong table.** It is fewer lines: 0058's `TyApp` table is four. But it holds every term the
process ever built. For types that bound is 808 and it is accepted. For terms it is millions per
chain and unbounded across chains.

**Interning only `Const`.** It is the largest ratio, 3818 objects per value, but 69 MB of the 345.
`App` is the rest.
