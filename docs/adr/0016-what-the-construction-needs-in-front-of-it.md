# 0016. What the construction of the reals needs in front of it, and what does not wait for it

- **Status:** accepted, extends 0007
- **Date:** 2026-09-15

## Context

[`0007`](0007-the-reals-are-constructed.md) decided that the reals are constructed and gave the
order: choice, infinity, the naturals, then the integers and the rationals as quotients, then the
reals as a completion. The first three landed on 2026-09-10 and the construction has not started.
Its own closing section says so.

What that record does not say is what has to happen **before** its step 4, and five measurements
taken on 2026-09-15 against the compiled chain, rather than against the sources, say that two of the
three things a reader would expect to be blockers are not, and that a third nobody had named is.

- **The arithmetic of `num` is already free of the reals, and the boundary falls at 74 against 17.**
  Three readings of `Peano`'s 91 published facts, taken at `1608454` in a worktree of its own so
  that another session's uncommitted work could not reach them. By statement: 74 mention no real
  anywhere, in the type of a leaf or in a constant they name, and 17 do. By axiom:
  `Derivation.axiomsOf` finds a real axiom under 15 of those 17, the two exceptions being
  `NUM_REAL_ZERO` and `NUM_REAL_SUC`, which unfold a definition and cost nothing. And by
  derivation, which is the reading that matters and the strongest of the three: walking all 91
  proofs node by node, **not one node of any of the 74 mentions a real**, in a conclusion or in a
  hypothesis. The same scan finds 1220 such nodes under `NUM_REAL_ADD` and 12032 under
  `NUM_FLOOR_LE`, which is what says the scan can see something.
- **`Ring` is not what closes a step about `num`, and cannot be.** Handed an equation of type `num`
  it refuses by type, *expected a term of type real*, and it refuses the reflexive one too. So the
  `Ring` that `Induct` holds is untouched by the pure stages: they take the induction skeleton from
  `Induct.proveBy` and close with `Peano`'s own private `settle`, which brings both sides to a
  normal form by rewriting with the recurrences. Five of the pure facts were re-derived against a
  closer that does nothing but reflexivity and cannot name a real: `NUM_ADD_ASSOC`, `NUM_ADD_SYM`,
  `NUM_MUL_ASSOC`, `NUM_POW_ADD` and, once `NUM_ADD_ASSOC` is in the rule set as the real stage
  supplies it, `NUM_MUL_DISTRIBUTE`. Each came out with the published statement, nothing assumed,
  two axioms, and no real node.
- **The developments above it are free of them too.** `Modular` 44 facts out of 44, `Language` 57
  out of 57, no axiom of the reals in any derivation. `Semiring` is why, and its own first paragraph
  gives the reason it was built: a theorem about the incompleteness of arithmetic that rests on the
  axioms of the real numbers is formally correct and says something false about what was needed.
  **That motivation for the construction is therefore already discharged**, by other means, and it
  should stop being offered as one.
- **`Product` is already below the line.** Its only call of `axiom` is `classical.axiom(Choice)`, so
  the pair type can be built under the reals without a change to it, which matters because the
  integers are carved out of a pair.
- **A quotient costs nothing beyond what the chain already holds.** The image of an equivalence
  relation, `\s. ?x. s = R x`, is a closed predicate, so `Kernel.defineType` takes it; the fact it
  is wanted for, `R x = R y <=> R x y`, needs function extensionality, and
  `Classical.FUNCTION_EXTENSIONALITY` is a derived theorem over eta rather than a further axiom.
- **What nobody had named: the report of a proof grows by three orders of magnitude.** An asserted
  axiom has `Derivation.size` 1. A fact about a carved type costs four figures, `PAIR_SURJECTIVE`
  1832. An identity decided by `RING` today is 2375 nodes resting on 8 axioms. `Derivation.walk`
  deduplicates by identity, so after the swap every theorem about a real carries the whole
  construction's shared graph, and the scale to compare against is a development's own total:
  `Peano` sums to 628902 nodes and `Language` to 904082. `Cost`, `Check` and every test that prints
  an inference count read that graph.

And one measurement that was already written down and is being read wrongly. `docs/evaluation.md`
records that 39 of miniF2F's 244 statements can be stated here, that 104 of the rest are blocked by
the syntax of a hypothesis and 18 by a type with no signature, and that the remainder name a
constant the theory has not got. **None of those blockers is the trusted base.** The row in
`README.md` that reads *"The integers, the rationals, sequences, limits: No, `docs/adr/0007` is the
order they arrive in"* puts four things behind one record, and only two of them are behind it.
Sequences and limits need a supremum and a notion of convergence, `COMPLETENESS` is already an
axiom a caller can apply, and `CompletenessSpec` applies it to a concrete goal today.

## Decision

**The construction of the reals is preceded by a split of `Peano`, and the split is its own piece
of work.** The 74 facts that name no real become a development below `Real` in the chain, and the
17 that do become one above `Order`. What decides which side a fact falls on is its statement and
not what it rests on: `NUM_REAL_ZERO` costs no axiom of the reals and still cannot be stated
without them.

**`Induct` takes its closer as a parameter instead of holding a `Ring`**, and the reason is
narrower than it looks. Nothing in the pure half ever calls that `Ring`, so this is not a closer
being replaced: it is a constructor demanding an argument a caller below the reals cannot build.
Four developments that are entirely about `num` were each threading one through their own
construction to satisfy it, `Modular`, `Coding`, `Numbering` and `Language`, and all four now take
a driver whose closer refuses by name. That they still build is the population-level version of the
measurement above: it is four whole developments rather than five sampled facts.
**The chain is not reordered yet, and that is a decision rather than an unfinished sentence.**
What phase 0 delivers is that the arithmetic **can** be built below the reals, asserted by building
it there: `Peano.arithmetic` runs the seven stages over a theory of the caller's choosing and
`ArithmeticBelowTheRealsSpec` runs them over `naturals.theory`, which has no type `real` in it.
The chain still puts the development over the reals, because moving it buys nothing until `Real`
is built over `num`, and that is phase 5. When it moves, the order becomes `Natural`, the
arithmetic of `num`, `Semiring`, `Product`, the construction, `Real`, `Arithmetic`, `Ring`,
`Order`, the embedding, and everything above unchanged.

**And it is not free, which was found by doing it rather than by planning it.** `numerals` widens
the notation so a digit string reads at `num` as well as at `real`, so running the pure stages
first made `real_of_num ZERO = 0` ambiguous **in its own statement**, and the chain stopped
building with exactly the refusal `docs/adr/0012` promises. The reader narrows and the text does
not gain annotations, which is what that record asks for; the general form of the problem is that
the notation is threaded through the chain the same way the theory is, so reordering one reorders
the other, and every statement about the reals carrying a bare numeral is where it shows.

**The guard on that split asserts the absence of the type, not the absence of the axioms.** A test
saying the 74 facts do not reach the sixteen would pass today and would pass again if the reals
crept back in through a lemma that happens to cost nothing. What cannot go vacuous is that the pure
development builds over a theory in which the type operator `real` is not declared.

**A quotient is a builder written once**, in the shape `Recursion` and `Descent` already have: a
Scala function over `Kernel.defineType`, not a polymorphic type of the object logic, since the
predicate names the relation and a relation is a particular constant. It produces the type, the
projection, `R x = R y <=> R x y`, the lifting of a unary and a binary operation against a
respectfulness obligation, and the lifting of a predicate. It is validated on a toy quotient before
the integers, and its test asserts that the axioms of what it produces **equal** the axioms of what
it was given, as `CodingSpec` does, rather than being contained in them.

**The construction lives in `modules/theories`.** It declares no new module.

**The sixteen become theorems under the same names, the same statements and the same printed
forms**, which is the property [`0004`](0004-reals-axiomatised-not-constructed.md) preserved on
purpose and which `RealSpec` already pins. `RealTheory` stops calling the map `axioms` in the same
change.

**The cost of the proof report is measured at the integers and not at the end.** The first quotient
gives a real figure to extrapolate from, and whether anything is done about it, a memoised walk or a
boundary in `Derivation` at a cited fact, is decided there while it is still cheap to decide.

**Analysis does not wait for any of this.** A supremum named by `select` over `COMPLETENESS`,
sequences, limits, and a square root are built over the reals as they stand. By 0004's preserved
property they survive the swap without a change, and they are what moves the measurement in
`docs/evaluation.md`, which the construction by itself does not.

### What this record does not decide

Two questions are left open deliberately, with what settles each.

**Which route the construction takes.** Either the integers as a quotient of `num` pairs, the
rationals as a quotient over them, and the reals as Dedekind cuts on the rationals, with
multiplication defined on the positive cone and extended by sign; or the positive rationals first,
the positive reals as cuts on them, and the reals as a completion of that positive cone, which
never meets a sign case and puts the integers off the critical path. Both are correct and they
share the whole of the quotient builder, so the decision is taken when that builder's cost is
measured rather than now. The first is the one to beat: the integers and the rationals are
themselves promised in `README.md`, and under it they arrive as a by-product instead of afterwards,
with one type of rational rather than two.

**How an operator is written at four numeric types.** `Notation` maps a symbol to one constant and
the reals own `+`, `*`, `<` and `<=`; `Peano`'s own docstring calls overloading by the type of the
arguments a change to the notation layer and to every consumer of it, and defers it. With the
integers and the rationals arriving, a user who writes `x + y` over the rationals has no way to say
so, and the deferral stops being affordable. That is a record of its own and it comes **before** the
integers, not after them.

## Consequences

**The trusted base does not move at any point of the work, and then drops to three.** 0007 predicted
a transition through eighteen or nineteen; that transition is over, the count has been nineteen
since 2026-09-10, no step below needs an axiom that is not already held, and what is left at the end
is choice, eta and infinity.

**Nothing a caller can state changes, except one thing.** `inv` becomes a defined constant, so
`inv 0 = 0` becomes a choice inside a definition and lines 65, 66 and 70 of the ring corpus stop
being an exception list. Everything else the construction buys is an answer to "what is this
believed on", not to "what can this say". Anyone judging the work by what the prover can newly reach
will judge it wrongly, and the analysis track above is the answer to that question.

**The report of every real theorem gets much larger**, by the measurement in the context. This is
the cost that has no upper bound written anywhere yet, and the reason the checkpoint is at the
integers.

**The rename reaches 108 call sites**, 79 of `axiom(` across 13 sources under `modules/*/src/main`
and 29 under test, counted on 2026-09-15.

**`docs/reading-register.md` loses sixteen rows and gains roughly forty**, one per constant the
construction declares, every one of them `NOT READ`. `RegisterSpec` goes red until it is
regenerated, which is the document doing its job.

**The coverage floor for `theories` falls until the tests arrive**, and it is read correctly only
after `clean`.

**The split touches the file with the most published facts in the repository.** `Peano` is 91 facts
and the largest source here. A split of it is not a refactor to be done in passing, and it is first
precisely so that it is not done in passing in the middle of a construction.

**The size, stated in what can be counted rather than in days.** Roughly 200 new published facts,
calibrated against this repository's own range of 35 to 105 lines per fact, which is on the order of
thirteen to fourteen thousand lines, or about thirty per cent of the theory corpus as it stands.
The least reliable part of that is the multiplication on cuts, which is why the route is chosen
after the builder is measured and re-estimated after the integers.

## Alternatives rejected

**Build a second copy of the arithmetic of `num` below the reals and leave `Peano` alone.** It
avoids splitting the largest file in the repository, and it is the failure
[`0008`](0008-a-constant-carries-what-defined-it.md) is about: two developments each defining
`NUM_ADD` produce different constants of the same name, so a claim naming the constructed reals and
`Sum` together would not be a proposition anywhere. `Chain`'s own comment records what that cost the
five developments that sat beside it until 2026-09-12.

**Canonical representatives instead of quotients**: an integer as a pair with one component zero, a
rational in lowest terms. It removes the builder entirely. Rejected because lowest terms need the
greatest common divisor, which is `Modular`, which would then have to sit below `Real`: a dependency
on the largest development in the chain, bought in order not to write the builder.

**Cauchy sequences on the rationals.** The usual construction, and multiplication is pointwise
rather than a case analysis. Rejected because completeness becomes the diagonal argument and the
inverse needs a sequence bounded away from zero, so the cost lands hardest on `COMPLETENESS`, which
is the one of the sixteen that is worth the most as a theorem: it is the axiom that separates an
ordered field from the reals, and until 2026-09-13 it was the one nothing read.

**The Eudoxus construction**, reals as almost additive functions on the integers modulo bounded
difference. It skips the rationals entirely and uses one quotient fewer. Rejected because nobody can
check it against a source in one sitting: the axioms here are written in concrete syntax for exactly
that reason, and a construction that reaches them by a route a reader cannot follow gives back what
the axioms' presentation was protecting.

**A module of its own for the construction.** Rejected because
[`0003`](0003-trust-boundary-is-the-module-graph.md) makes the module graph the trust boundary, and
this work moves nothing across it: no axiom, no kernel change. A module would buy a line in a
diagram and no guarantee.

**Keep `RealTheory.axioms` as the field name after the swap.** It is the smallest possible change
and every call site keeps working. Rejected because the name would then say axiom about a theorem,
in the one place in this repository where the difference between those two words is the whole point.

**Wait for the construction before building sequences and limits.** It is what the README row
implies today. Rejected on 0004's preserved property: analysis written over the sixteen as axioms is
identical to analysis written over the sixteen as theorems, so waiting buys nothing and costs the
whole duration of the construction.
