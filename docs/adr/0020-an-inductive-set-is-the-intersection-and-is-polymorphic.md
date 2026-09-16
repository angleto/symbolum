# 0020. An inductively defined set is the intersection of the closed sets, and it is polymorphic

- **Status:** accepted
- **Date:** 2026-09-16

## Context

One definition in three of rewriting theory is given in one shape: *the least subset of `Sigma*`
containing X and closed under the following clauses*. Until this record, that shape could not be
**written** in this repository. There was no least fixed point of a monotone operator anywhere:

    git grep -l 'InductiveSet' 518859b -- '*.scala'    # empty
    git grep -l 'least set'    518859b -- '*.scala'    # empty

What could be done instead was to generate the closure forwards to some depth and look. That
answers a membership, for the members the budget reached, and it answers **nothing** about a
non-membership: an element that is not in the set is indistinguishable from one that is further
away than the budget. The consumer that made this pressing is the Collatz repository's `05`
§3.1.30, where `RFC(S_2)` is exactly a definition of this shape, membership of a family is proved
in two lines by hand, and both halves live in `code/referee/checks_rewriting.py` as checks over
instances rather than as theorems. A document that marks such a paragraph `[proven]` is resting on
a hand proof no kernel has read.

The construction itself was not missing, only its generality. `Natural.NUM_REP` carves `num` out of
`ind` as the smallest set holding `IND_0` and closed under `IND_SUC`, written as a predicate, and
its own comment already contains the sentence this record generalises: *induction is then not a
further assumption, it is this definition read back*. What was missing was that trick for an
operator the caller brings.

## Decision

An inductively defined set is the **intersection of every set closed under the operator**, taken as
a definition rather than built by iteration:

    MONOTONE  = \f. !S T. (!x. S x ==> T x) ==> (!x. f S x ==> f T x)
    INDUCTIVE = \f x. !S. (!y. f S y ==> S y) ==> S x

It is **polymorphic in the element type**. `INDUCTIVE : (('a -> bool) -> 'a -> bool) -> 'a -> bool`,
and nothing in `modules/theories/.../Inductive.scala` mentions a number, a word or a pair.

Its two faces are two facts and not one, because they cost different things:

- `INDUCTIVE_INDUCT`, that an `f`-closed `S` contains the closure, asks **nothing** of `f`. It is
  the definition unfolded and specialised. It is what proves a non-membership.
- `INDUCTIVE_INTRO`, that the closure is itself `f`-closed — the introduction rules of the rule set,
  all at once — asks `MONOTONE f`.
- `INDUCTIVE_FIXPOINT` is the two together and is derived from them, which is what entitles the name
  "fixed point".

Monotonicity is an obligation on the caller, discharged per rule set, and there is no procedure that
decides it.

## Consequences

**A non-membership becomes a theorem.** That is the whole return, and it is the half that could not
be obtained by computing. `InductiveSpec` derives `~(EVEN (SUC ZERO))` for the even numbers as the
least set holding `ZERO` and closed under two successors, using no monotonicity at all.

**Every rule set pays a monotonicity proof.** Measured rather than estimated: a two-clause operator
costs about forty lines of `InductiveSpec`. Every operator written in the usual shape — a
disjunction of clauses in which the set argument occurs only positively — is monotone, so a
procedure recognising that shape syntactically would remove the cost entirely. It is not written,
and that is the gap this record names.

**`Chain.widest` moves again.** This link declares two constants, so it is the widest signature. It
is the ninth name that field has held in five days, which is the argument the field's own comment
now makes for not writing the current one in prose anywhere.

**`Natural.NUM_REP` is not refactored to use this, and will not be.** It is below this link, so it
cannot see it; and `Kernel.defineType` wants a closed predicate over `ind`, which `INDUCTIVE f`
applied to a concrete operator is. The duplication is real and is the price of the layering, which
`docs/adr/0003` already fixes. What a reader should take is that the hand-written one is the worked
example of the general one, not that one of them is redundant.

**Nothing in the trusted base moves.** Two definitions, no axiom. The facts of this development cost
what the logic under them costs and no more.

## Alternatives rejected

**Iterating the operator to a fixed point, which is the Kleene construction.** Attractive because it
is the picture everybody has of an inductive definition, and because it would make membership
constructive: a member appears at some finite stage. It loses on what it needs in front of it. Over
`num` alone it reaches only the first omega stages, so it is correct only for a **finitary**
operator and would carry that hypothesis into every statement; a clause quantifying over an
unbounded family is exactly what `RFC`'s inside-reduction clause looks like once the rewriting
relation is there. Going past omega wants ordinals, which this repository does not have and which
`docs/adr/0007` puts far later than the integers. The intersection needs none of it: no recursion,
no limit, no ordinal, and no finitarity hypothesis. It is also **shorter** — the induction principle
is the definition read back, where the iterative version would have to prove it.

**Defining the closure over `word` directly**, which is what the card asking for this assumed by
writing the potential function as `Phi : word -> num`. It loses on two counts. Nothing in any of the
three facts, or in the potential-function lemma above them, mentions a word: the relation is
abstract, the potential goes to `num`, and the induction is on the derivation. And it would have
made this work wait on `WORD_CONCAT`, which is a separate card held by a separate session, for no
reason other than where the statement happened to be written first. What genuinely needs the
concatenation is one line — the step `u ->_R v` of a string rewriting system, which says the
left-hand side is a **factor** — and it is the last line rather than the first.

**Asserting the introduction rules and the induction principle per rule set**, which is what an
inductive-definition package does when it does not derive them. Rejected on the standing rule of
this repository, that a result is added by proving it; and the cost of keeping that rule is nil
here, since `Natural.NUM_REP` had already shown the derivation is under thirty lines. Asserting
would also put the monotonicity condition nowhere: each assertion would be sound only under a
hypothesis nobody wrote down, which is the defect `STM-01` describes in general and which this
repository has paid for once already in `docs/adr/0008`.

**Making `MONOTONE` a hypothesis written out at each call site rather than a defined constant.**
Rejected because a condition that every caller states inline is stated differently by each of them,
and then nothing can be proved once about the class — including the procedure, named above as the
gap, that would decide it.
