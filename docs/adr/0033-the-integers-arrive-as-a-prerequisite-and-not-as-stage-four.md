# 0033. The integers arrive as a prerequisite, not as stage four of the construction

- **Status:** accepted, extends 0016
- **Date:** 2026-09-18

## Context

The chain declared four type operators — `num`, `real`, `prod` and `word` — and no signed ring.
Mycelium card `f6368d8d` is what says that absence costs something now rather than eventually, and
the half of it worth carrying is that it blocks two open formalisations of the `collatz`
repository's `documents/02` in **two different ways**, neither of which is a file sitting in the
wrong place:

- `Divisibility` is built over the reals, and in a field every non-zero element divides everything.
  That is not an awkward edge: `DIVIDES_NONZERO` is `!a b. ~(a = 0) ==> Divides a b`, derived in
  that file with nothing assumed. A divisibility hypothesis stated there is discharged
  **vacuously**, so a development that carried one would be checking nothing and would look exactly
  like one that was.
- `NUM_DIVIDES` is over `num` and cannot state the condition at all, because the coefficients the
  argument divides are lattice coefficients and are signed.

The two consumers are real and both are already settled by hand on the other side:
`02 s2.7(e)`, the `Z` basis of the phase-collision lattice, which reduces to the triangular system
`2^{f-j_i} | lambda_{i-1} - 3 lambda_i` over signed coefficients; and `02 s2.6(c)`, the 2-adic
valuation of `det_h`, whose determinant entries are signed. What cannot be done is to **state**
either in this kernel.

[`0007`](0007-the-reals-are-constructed.md) already has the integers: they are step 4 of its
roadmap, *"the integers and the rationals as quotients, then the reals as a completion"*.
[`0016`](0016-what-the-construction-needs-in-front-of-it.md) sizes that whole programme at roughly
200 published facts and thirteen to fourteen thousand lines, and leaves open which of two routes it
takes.

## Decision

**The integers are built now, as a thing that stands on its own, and not as the opening move of the
construction of the reals.**

The distinction is not presentational and it is the whole of this record. Under the construction's
framing this work is estimated as the large piece, scheduled behind a decision about Dedekind cuts
against Cauchy sequences, and never started; what the card asks for is the part that stands up
alone. An ordered ring of integers with a divisibility over it needs **no** rational, **no**
completion and **no** axiom of the reals to become a theorem, and the two consumers need exactly
that and nothing above it.

**The route is `0016`'s first, the quotient of `prod(num,num)`,** and the decision was deferred in
that record until the quotient builder's cost had been measured. It has been: `Quotient` landed on
2026-09-15 and was validated on `num` modulo two before anything real was built through it, which
is what `0016` asked for. This is its first real consumer, and what it cost is recorded in the
consequences below.

**The relation is `FST p + SND q = FST q + SND p` and carries no subtraction.** `num`'s subtraction
is truncated, so `FST p - SND p = FST q - SND q` is a different relation and is not an equivalence:
`(0,1)` and `(0,2)` both truncate to zero and stand for different integers. The additive form is
the standard one and it is chosen here for a reason that can be stated rather than for tradition.

**The operations keep a prefix spelling: `INT_ADD a b` and not `a + b`.**
[`0018`](0018-an-operator-symbol-stands-for-more-than-one-constant.md) lets a symbol stand for more
than one constant and `+`, `*`, `<` and `<=` already stand for two, the reals' and `num`'s. A third
candidate is not a line in `Notation`: the elaborator refuses a text nothing determines, so every
existing statement carrying one of those symbols gains a way of being ambiguous. When `num` joined
the overloading, 135 statements of the library changed text. That is a measurement of its own and a
card of its own, and putting it inside this one would mean the integers landing or not landing
according to whether a notation change went well.

**Which development is `Chain.widest` is not written here**, for the reason `Chain.widest`'s own
docstring gives. What is written here is that this link extends the chain's end rather than sitting
beside it, and the argument is the one the five developments moved into the chain on 2026-09-12
were moved by: a constant declared into a side branch is unreachable from everything, its facts
reach no library, and `docs/lemmas.md` does not list them.

## Consequences

**The trusted base does not move.** The type is `Kernel.defineType` over the image of a closed
relation, the operations are lifts, and every fact costs what the carrier cost: choice, eta and
infinity, which is what the naturals and the pair already cost. `IntegerSpec` asserts that as an
**equality** of axiom sets rather than as a ceiling, which is the form `CodingSpec` uses, and for
every other statement it asserts a **containment** in those three. A signed ring that charged the
sixteen would be a ring built on the thing it exists to avoid needing.

That sentence said the spec asserted separately that no axiom of the reals is among them, and it
was written from the shape of the check rather than from the check. Read on 2026-09-19 the loop
compared each statement against **one** of the sixteen, `ADD_SYM`, so a statement resting on
`COMPLETENESS` or on any of the other fourteen passed. The repair is the containment above rather
than a loop over all sixteen, because containment refuses those and also refuses a seventeenth
axiom arriving from anywhere else, which nothing was watching for. The blanket **equality** over
every statement, which is the other form and looks stronger, is false: `INT_SAME_REFL` is one of
them and the next assertion in that file says it does not reach choice. What makes the containment
say anything about the reals is that the sixteen are outside those three, which is now asserted
rather than assumed, and `IntegerSpec` exhibits an axiom the old reading accepted and this one
refuses rather than claiming the difference.

**The type does not collapse, and that is derived rather than assumed.** `QuotientSpec` says in as
many words that non-collapse is the one guard it cannot carry: refuting it there means deriving
`~(NUM_CONG 2 2 3)`, which nothing in this repository can, so that file's evidence is structural.
Here it is not. `num` has `Successor.distinct`, so `~(INT_OF_PAIR (PAIR 0 0) = INT_OF_PAIR (PAIR 1
0))` is derived from `~(0 = 1)` with nothing assumed, and the injectivity of `INT_OF_NUM` says the
same thing for every pair of naturals. A one-point `int` satisfies every equation in the
development and refutes both of those.

**Every ring law is one function applied to a pair of texts, and a further one costs a line.** Both sides of an equation
between integers are written at carrier variables; the lifted equations and the two projections of
a pair rewrite each side to a single `INT_OF_PAIR` of a pair; `Semiring` decides the resulting
identity of the commutative semiring on `num`, at no axiom of the reals; the quotient's central
fact turns that into an equation between classes; and the statement is put back over `int` by
specialising at a representative. How many laws there are is deliberately not written here: the
number is `Integer.Statements`, `IntegerSpec` compares every entry of it against the theorem proved
under that name, and a figure repeated in prose is the copy that drifts. What that route cannot do
is a law that is **not** a semiring
identity after projection, and the two in the file that are not say so where they are written: the
respectfulness of multiplication, which multiplies a premise rather than rearranging it, and the
injectivity of the embedding, which is a biconditional and not an equation between integers.

**The quotient builder's docstring is wrong about its own first consumer, and the correction was a
reading before it was a run.** That file said it lifts "no function whose result is not quotiented
(`num`-valued, say)", and named the integers as the consumer that does not need one. The bridge to
`real` is exactly such a function, so the sentence was false about the thing it named. What was
measured on 2026-09-18, before the bridge existed, is that the code does not say it: `Type.Bool`
appeared at seven lines of `Quotient.scala` and not one of them was inside `liftPredicate` or
`checkPredicate`, which build their equation with `Term.eq` at whatever type the operation returns
and carry it with `Conv.sym` and `Conv.trans`, neither of which is about propositions. **The
prediction written here was that it lifts the bridge unchanged.**

**It was run the same day and it held, and what it did not predict is the more useful half.**
`Inclusion` lifts `\p. real_of_num (FST p) - real_of_num (SND p)` through `liftPredicate` with no
change to that method at all, and `INT_REAL_PAIR` is what comes back. What the builder was
nevertheless missing is a second thing, and it is not about the result type: **a lift defines its
constant into the quotient's own theory**, which is the theory as it stood when the last lift ran.
The integers lift three operations and then define `INT_ZERO`, `INT_ONE`, `INT_OF_NUM`,
`INT_DIVIDES` and `INT_LE`, so `Integer.quotient.theory` carries 140 constants against
`Integer.theory`'s 145, measured on 2026-09-18, and `real_of_int INT_ZERO = 0` could not have been
**stated** against it. `Quotient.over` re-bases a quotient onto a theory extending it, checked by
`Logic.over`, which is what the consumer calls first and is the whole of the addition.

So the reading was right about what it looked at and blind to what it did not: it asked whether the
method reads the result type and answered correctly, and the obstacle was one theory earlier. That
is worth keeping because the prediction was written down before the run and both halves are
therefore legible — which is the argument for writing it down, not an argument that a reading
substitutes for a run.

**Nothing becomes a theorem that was an axiom**, and nothing a caller could state stops being
statable. This is an extension of the signature and not a change to it.

**The order is the one construct the quotient builder does not reach, and that is a measurement of
that builder rather than a complaint about it.** It lifts a unary operation, a binary one and a
predicate of one argument. A relation of two quotient arguments is none of the three: `liftBinary`'s
obligation relates the two **results**, which needs them in the carrier, and a proposition is not in
it. So `INT_LE` is defined through the chosen representatives here and `INT_LE_PAIRS` is derived
from a respectfulness lemma of its own — which is the shape a fourth lift would have, written once
in its first consumer rather than added to the builder ahead of one, which is the criterion 0016
sets for that file.

**What is not here, named so that the list does not go stale silently.** The list this paragraph
carried is empty as of 2026-09-19, and it is rewritten rather than ticked, because what its two
open entries cost is not what it predicted. What is missing from the development now is one thing
it never listed, the rationals, and `CLAUDE.md` is where that is written.

It said a concrete non-divisibility at a non-zero divisor — `~(INT_DIVIDES 2 1)` — needed the
discreteness of the order, that nothing lies strictly between zero and one, and that the converse
of `NUM_DIVIDES m n ==> INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n)` needed the same lemma because
the witness has to be shown non-negative. **Neither needs it, and no such lemma was written.** The
two are one fact, `INT_DIVIDES_OF_NUM`, which is the biconditional rather than either implication
for the reason `INT_LE_OF_NUM` is one; and under it the refusal is `Modular.NUM_DIVIDES_ONE` at two
numerals. `IntegerSpec` walks the refusal's derivation and asserts that no fact of `INT_LE` is in
it, with a positive control beside it so an empty answer cannot come from an instrument that read
nothing.

What the prediction got wrong is worth more than the correction. The witness of the divisibility is
an **integer**, so reading it back as a natural is the step that wants a sign argument, and the
route taken does not ask: `INT_CASES` writes the witness as some pair, the equation between classes
becomes `n + m * b = m * a` between naturals, and `Modular.NUM_DIVIDES_SUMMAND` concludes without
anything deciding which of `a` and `b` is the larger. There is no case split in the section. The
arithmetic that bounds the divisors of a non-zero number was already proved one type down, and a
faithful embedding is how a fact of that kind travels; deriving discreteness here would have
rebuilt it.

The third entry was already answered when this was written. The bridge to `real` **is** here, as
`Inclusion`, landed 2026-09-18 and the link that ran the prediction above, and so is the order,
`INT_REAL_LE`, later the same day. It did want an argument of its own rather than the
rewriting route the equations share, and what it wanted first was a fact one type down: the library
carried `NUM_LE m n ==> real_of_num m <= real_of_num n` and not its converse, so the right-to-left
half of the biconditional had nothing to cross on. `Peano.NUM_REAL_LE_BACK` is that converse. What
the order map does **not** do is settle the non-divisibility above it, and since 2026-09-19 that is
a measurement rather than a question: that statement is proved, `IntegerSpec` finds no fact of
`INT_LE` in its derivation, and this map cannot be in it because `Integer` is built below
`Inclusion`. So the map remains the instrument by which an order fact of the reals would reach
`int`, and it has no consumer.

## Alternatives rejected

**Wait for the construction of the reals and take the integers as its step 4.** It is what `0007`
and `0016` schedule, and it is what leaves both consumers blocked for the duration. Rejected on the
card's own argument: the estimate that stops this work is an estimate of the whole programme, and
none of what the two consumers need is above this link. Nothing in this record forecloses the
construction — the file reaches for no real except in its bridge, so the link moves below `Real` at
phase 5 rather than being rewritten, and `Embedding.scala` is the precedent for where the bridge
goes when it does.

**Canonical representatives: an integer as a pair with one component zero.** It removes the
quotient builder entirely and `0016` already rejected it, in the general form: the same trick for
the rationals wants lowest terms, which wants the greatest common divisor, which would put
`Modular` below `Real`. Repeated here because for the integers **alone** it is genuinely cheaper,
so a reader who sees only this file would take the rejection for an oversight.

**Define `int` as the subset of `real` carved out by `?n. x = &n \/ x = --(&n)`, which is what HOL
Light does.** It is much less work: the ring, the order and the bridge all come from the reals'
axioms and nothing is lifted. Rejected because it inverts the dependency the construction needs: an
`int` defined over `real` cannot be what `real` is later constructed from, so the work would be
done twice and the second time from scratch. It also charges the sixteen axioms to every theorem
about an integer, which is the price `Semiring` exists to avoid paying and which the two consumers
would inherit.

**A module of its own.** Rejected for `0016`'s reason, which is
[`0003`](0003-trust-boundary-is-the-module-graph.md): the module graph is the trust boundary and
this work moves nothing across it. A module would buy a line in a diagram and no guarantee.

**Overload `+`, `*`, `<` and `<=` at `int` in the same change.** Rejected above, and recorded here
as a rejection rather than as a deferral because the difference matters to whoever picks it up: the
work is a measurement of what the third candidate does to the 136 statements that moved last time,
not a line of `Notation`.
