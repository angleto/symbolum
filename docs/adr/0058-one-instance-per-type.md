# 0058. One instance per type, because a chain spelt 808 types with 4.4 million objects

- **Status:** accepted
- **Date:** 2026-09-27

## Context

`theories/test` runs its suites in one forked JVM at `-Xmx1024m`, and every suite there reads the
one `Chain.standard` that fork builds. Mycelium card `78c1381d` measured that fork at 714-767 MB
after compaction at `7a15f023` and said the next link that grew the chain would kill it. On
2026-09-27 that happened: the work of the sessions that crashed that afternoon, integrated onto 7.0
`fced4c8f` as branch `integrate-0927` at `cf853ffa`, died of `OutOfMemoryError` in that fork, while
`theories/test` on 7.0 alone passed, 1378 green.

The card asked which suite carries the peak. **None does: the chain does.** Measured with a probe
that builds `Chain.standard` and reads the used heap after four `System.gc()` calls, `-Xmx4g`:

| tree | live after the chain | chain built in |
|---|---|---|
| 7.0 `fced4c8f` | 677 MB | 26.8 s |
| `integrate-0927` `cf853ffa` | 703 MB | 25.1 s |

So two thirds of the fork's heap is taken before the first assertion of the first suite, and
growing the chain by 27 MB was enough to cross the line. What the chain is made of was the next
question, and a class histogram of that heap (`jcmd GC.class_histogram`) answered it in a way no
reading of the code had suggested:

| class | instances | MB |
|---|---|---|
| `kernel.App` | 8.24 M | 189 |
| `::`, a list cell | 7.87 M | 180 |
| `kernel.TyApp` | 4.44 M | 102 |
| `Kernel.Thm` | 2.26 M | 52 |
| `kernel.Const` | 1.79 M | 41 |
| every `Derivation` node together | about 2.3 M | about 50 |

The proof record, which was the suspect, is a small part of it. The list cells are not the
hypotheses either, which was the second suspect. A census walking every theorem reachable from the
library's 930 facts through `Derivation.premises`, each object counted once by identity, attributes
them: 2 256 890 theorems, which is every `Thm` in the heap; **4.32 million `TyApp` and 7.25 million
cells of their argument lists reached from conclusions alone, spelling 808 distinct types**; 0.46
million cells of hypothesis lists. At 24 bytes an object, types were about 280 MB of a 700 MB
chain.

They are copies because nothing in the kernel shares a type once it is built. `Type.fun` allocates,
`Type.substitute` rebuilds a ground type it does not change, and every equation a rule constructs
carries `=` at `ty -> ty -> bool`, built afresh each time.

## Decision

**`TyApp` has one instance per value.** Its constructor is private and its companion's `apply` looks
the candidate up in a `ConcurrentHashMap` and returns the instance already there, inserting it with
`putIfAbsent` when there is none. Its hash is computed once and kept, as `App`'s and `Abs`'s are,
because a lookup hashes on every construction.

Nothing else moves. **Equality stays structural**, so no rule, no comparison and no theorem can
depend on which instance a caller holds: interning changes how many objects there are and nothing a
kernel operation computes. Every existing construction `TyApp(op, args)` in the repository already
goes through `apply`, so no caller changes, and pattern matching is untouched.

**The trusted base bound goes from 1220 lines to 1240.** The four files were 1215 lines, the change
is sixteen with its comments, and it belongs inside the count rather than beside it: a table that
handed back the wrong instance for a key would change what a term says, which is exactly the kind
of defect the counted files are the ones that can have. `DocumentationSpec` holds the bound and the
documents that quote it.

**On 2026-09-28 the verification of card `78c1381d` found a second route.** A private constructor
makes `copy` private too, but Scala 3 still synthesises a public `fromProduct` on the companion,
and it called `new` directly: `TyApp.fromProduct(("bool", Nil))` was equal to `Type.Bool` and not
the same instance. Nothing called it, so no result changed; the sentence "built only by `apply`"
was false. The companion now writes `fromProduct` out through `apply`, seven lines inside the same
bound, and `TypeInterningSpec` asks both it and the derived mirror.

## Measured

Same probe, same flags, on `integrate-0927` with only the kernel's classes replaced by the
prototype's:

| kernel | live after the chain | chain built in |
|---|---|---|
| as it was | 701 MB | 25.1 s |
| **one instance per type** | **429 MB** | 16.6 s |
| that, and the traversals below sharing what they do not change | 401 MB | 13.2 s |

Each build time is one run and is quoted as that. The memory figures are the used heap after
collection, which is not the same criterion as card `78c1381d`'s occupancy after a full compaction
pause; the fork's figure after this change, read by that criterion, is below.

**The fork, after.** `tools/sbt test` on `integrate-0927` with this change and `-Xlog:gc` added to
`theories / Test / javaOptions` for the run: `theories` ran to the end, 1432 green and one red that is
not about memory (`SeriesFragmentBoundarySpec`, card `7bf9d8a2`), where the same tree without the
change had died in `ExpanderPigeonholeSpec` and never reached the suites after it. **The log holds
no `Pause Full` at all**, where card `78c1381d` counted two in the shared fork and six with
`ChainSpec` inside it, each preceded by an evacuation failure. So the criterion that card read,
occupancy after a full compaction, has no reading here: G1 never needed one. What the log does hold
is occupancy after the concurrent cycle's cleanup, 595 to 844 MB across the run; that figure carries
the garbage the cycle has not yet reclaimed and is not the live heap, and it is quoted so that the
next measurement has something of the same kind to be set against, not as the margin.

`TypeInterningSpec` in the kernel's tests asserts identity, `eq`, for a type built directly and
through `Type.fun`, for the result of `Type.substitute`, for the type inside the `=` of an equation
`Term.eq` built, and for one type built on sixteen threads at once. All four were seen failing with
`Type.scala` as it was and passing with the change.

## What it does not reach

**Terms.** `App` is now the largest class, 8.2 million instances, and the census found at most 1.1
million distinct terms of every kind together. Hash-consing terms is the same idea at a thousand
times the table size, which makes a strong table a leak across chains and a weak one a new
mechanism in the trusted base; it is not decided here.

**The table only grows.** It holds every distinct type the process has spelt, which is 808 for a
whole chain and bounded by that for the suite; a caller that generated types without bound, such
as a property test drawing random operators, grows it for the life of the JVM. No such caller exists
today, and the bound on it is the number of distinct types rather than the number of uses.

**What is retained.** A chain still keeps every intermediate theorem of every derivation, 2.26
million of them, because a report walks them; this makes each smaller and does not make fewer.

## Rejected

**Raising the fork's heap.** Card `4222de0a` rejected it with a measurement and card `78c1381d`
repeated that it was not a proposal: the fork runs beside a launcher on a machine whose free memory
was measured at 85-207 MB during a coverage run, and a heap that grows with the chain buys one more
link each time.

**Splitting `theories/test` into more forks.** The forks run one at a time, so a split costs time
rather than memory: every fork builds its own chain, about 25 s at `cf853ffa`. What it does not buy
is room, because each fork still holds a whole chain before its first suite runs, and the chain is
what grows. `4eae217e` split `ChainSpec` into a JVM of its own for the one suite that built a
second chain, and `812e8c81` replaced that grouping with `OneChainPerForkSpec`; neither addressed
the size of the first.

**Sharing in the traversals alone** (`Term.substitute`, `substituteTypes`, `open`, `close`,
`Type.substitute` returning the node they were given when nothing under it changed). Measured
above: 701 to 650 MB by itself, 28 MB more on top of interning, for more lines in `Term.scala` than
this change spends in `Type.scala`. It is correct and it is left for when the terms are decided,
since it is part of that question rather than of this one.

**Dropping the proof record.** Every accounting in the system, `Derivation.axiomsOf`,
`Real.spent`, `RestsOn`, the checker's replay, walks it, and it is about fifty megabytes of the
seven hundred.
