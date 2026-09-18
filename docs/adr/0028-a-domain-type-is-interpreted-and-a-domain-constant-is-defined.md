# 0028. A domain's type is interpreted at the build, and a domain's constant is defined rather than declared

- **Status:** accepted, extends 0024
- **Date:** 2026-09-18

## Context

`docs/adr/0024` decided how a claim about a domain reaches the foundation's arithmetic, and kept
one refusal: a claim needing arithmetic about a **type** the domain declares and the foundation has
never heard of. `Cost` as a type operator with `Expensive : cost -> bool` has no arithmetic content,
nothing anywhere relates `cost` to a number, so there is no bridge to name and — since
`docs/adr/0027` — none to find either. That record says the interpretation is where that case gets
built, and this is that piece.

Two measurements on the standard chain, 2026-09-18, decide its shape, and both are in
`InterpretationSpec` rather than in this paragraph.

1. **A domain that declares its constants over `num` already gets the arithmetic, today, with
   nothing new.** `Expensive : num -> bool` with the axiom `!c:num. Expensive c ==> NUM_LE 3 c` and
   a named bridge settles `!c:num. c < 3 ==> Approved c`. Nothing about `Domain` prevented that and
   nothing ever did: the retry rule of `0024` is the same shape, with `Attempts : job -> num`. So
   whatever the missing capability is, it is **not** "a domain may mention foundation types".

2. **The wall a domain's own type hits is the parser, not the refusal.** With `cost` declared,
   `!c:cost. NUM_LT c 3 ==> Approved c` does not typecheck: `NUM_LT` wants a `num` and `c` is a
   `cost`. That is a **type error**, not a verdict, so it is not something `settle` could lift by
   deciding differently. The claim `DomainTheorySpec` refuses — `NUM_LE 3 3 /\ Expensive c ==>
   Approved c` — parses only because its arithmetic is closed and inert.

The second measurement is what makes this a decision rather than a lifting of a refusal. A claim
about a domain type needing arithmetic cannot be *stated*, so an interpretation has to act where
the claim is read, which is when the domain is built.

## Decision

**`Domain.build` takes an `Interpretation`, which is two maps and they are two different kinds of
thing.**

**A type of the domain becomes a type of the foundation.** `cost -> num` means the build declares
no `cost` at all and declares the domain's constants over `num` instead. It asserts nothing, defines
nothing, costs no axiom, and changes no accounting. What it buys is that a claim about a cost can be
written, which measurement 2 says is the whole obstacle.

**A constant of the domain becomes a definition rather than a declaration.** `Expensive -> "\c:num.
NUM_LE 3 c"` means `Kernel.defineConstant` rather than `declareConstant`, so the constant stops
being an atom with nothing inside it. It costs no axiom either, and `docs/adr/0008` gives it an
**origin**: two builds of one description under different interpretations produce constants that
are not equal, which is the one place this arrangement is safer than a declared name rather than
riskier.

**A partial interpretation is the ordinary case.** A name in neither map is declared exactly as it
was, and the usual shape is a subject type interpreted with the predicates left abstract.

**A meaning reaches a decision as two implications, not as its defining equation.**
`Kernel.defineConstant` hands back `|- Expensive = \c. NUM_LE 3 c`, and equality is not one of the
five connectives, so at the skeleton `Expensive c = NUM_LE 3 c` is a single atom and decides
nothing. `Domain.Built.meaningOf` derives `|- !x. (Expensive x ==> NUM_LE 3 x) /\ (NUM_LE 3 x ==>
Expensive x)` out of the derived rules, at no axiom, and that is what a caller hands to `settle` as
a bridge — named at the call site, exactly as `0024`'s library lemma is.

**The report gains a column, and it reports what the conclusion RESTS ON rather than what it
mentions.** `Domain.Spending.defined` names the interpreted constants whose meaning took part in
the derivation.

## Consequences

**A reader of a domain claim now has two things to check rather than one.** A conclusion resting on
an axiom rests on something a reader can argue with; the same conclusion resting on `Expensive`
*meaning* `3 <= c` rests on that being the right translation of the word, and no axiom column would
ever say so. That is the honest cost of interpreting, and `defined` is where it is paid.

**The first version of that column reported the interpreted names the conclusion mentions, and it
was empty in exactly the case it exists for.** `!c. c < 3 ==> Approved c` does not mention
`Expensive`: the meaning was spent on the way and is gone from the statement. The derivation is
walked instead, by `Derivation.restingOn`, which is the same instrument `Library.restingOn` uses.

**Asserting an axiom about a defined constant is now possible and is the caller's to answer for.**
The kernel permits it, and an axiom contradicting a definition makes the theory inconsistent. That
is the same standing the file already gives to contradictory axioms, and it is worth naming because
an interpretation makes it easy to reach by accident: a rule that says what `Expensive` implies,
plus a meaning saying what `Expensive` is, are two statements about one word.

**`meaningOf` covers a constant answering a proposition and refuses the rest, by name.** A constant
interpreted as a function into `num` — `Size : cost -> num` as `\c. c` — is interpreted just as
usefully, and what a claim about it needs is rewriting rather than a propositional skeleton. That is
a different piece of work; handing back something that looks like a bridge and decides nothing would
be worse than the refusal.

## Alternatives rejected

**Declaring a measure into the foundation instead, `Size : cost -> num`, with no interpretation at
all.** This works today, it is the retry rule's own shape, and for many domains it is the better
answer: a cost is not a number, it *has* one. It is rejected as the general answer for one reason,
which measurement 1 and the acceptance test between them show: the measure leaves `Expensive` an
atom. A claim that turns on what "expensive" means cannot be settled by any amount of arithmetic
about the measure, because nothing relates the predicate to it except an axiom the caller would have
to assert — and asserting it is exactly what an interpretation replaces with a definition that costs
nothing.

**Interpreting only types.** Smaller, and it is genuinely half the capability: it makes the claim
writable. It is not enough for the card's own example, because a writable claim about an opaque
predicate is still a claim about an opaque predicate. Both halves land together, and a caller who
wants only the first passes `Interpretation.ofTypes`.

**Interpreting a constant by rewriting the claim before deciding it.** The obvious alternative to a
definition: substitute the meaning into the goal and decide what comes out. It reaches the same
answers on this example and it loses the accounting, which is the whole of what this file is for.
The theorem would be about the rewritten claim, `Derivation` would have no record that a translation
happened, and `defined` could not be computed at all.

**Putting the meanings into `settle` automatically, so that a caller need not name them.** It is
convenient and it breaks `0024`'s discipline at the site where the discipline matters most: what a
conclusion about somebody's domain was allowed to use should be visible where somebody asked for it.
A caller that wants them all writes one `map`, and the call site says so.

**Rewriting the axiom texts through the map, so one description reads in both builds.** The texts
mention the domain's type in their annotations, and a build that interprets `cost` cannot parse
`!c:cost. ...`. Rewriting the string is fragile in the way this repository refuses elsewhere. What
is done instead is nothing: an annotation the interpreted build cannot read is a parse refusal
naming it, and a description meant for both builds leaves the binder to be inferred — which
`InterpretationSpec` does, with `!c. ~(Expensive c) ==> Approved c` read in both.
