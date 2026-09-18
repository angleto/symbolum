# 0024. A domain claim reaches arithmetic through named bridges, not through an interpretation

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`Domain.Built.settle` decides a claim about a domain that is not mathematics: it specialises the
domain's axioms at the subjects the claim names, decides the propositional skeleton with every
domain constant an atom given no meaning, cuts the instances down to an irredundant set, detaches,
and reports what it spent. `docs/adr/0022` decided that the skeleton goes to the intuitionistic
calculus first, so the ordinary case costs no foundational axiom at all.

A claim that mentions a constant of the foundation is **refused by name**:

    a claim in the retry rule's own vocabulary: NUM_LT belongs to the foundation underneath it,
    and an atom with no meaning is not an approximation of arithmetic

The refusal is right and `DomainTheorySpec` has asserted it since it was written. What it blocks is
the shape every real criterion has: *at most three attempts*, *ships within two days*, *no more than
one reviewer*. A rule engine that cannot count is a rule engine for a small set of rules.

The obvious repair, and the one this record exists to reject in that form, is an **interpretation
map**: say that the domain's constant `Attempts` means some term of the chain, hand the claim to
`Linarith` or `Ring` with that meaning substituted, and get an answer. It is the repair the card
that asked for this work proposed, in the order *interpretation first, then the refusal is lifted*,
on the argument that lifting the refusal without a meaning would approximate an atom with a number,
which is the failure the refusal prevents.

That argument is right about a case and wrong about **the** case, and the difference was measured
rather than reasoned. `DomainTheorySpec`'s own example is:

    Attempts  : job -> num
    Abandoned : job -> bool
    axiom     AbandonedOnlyAfterThree   !j:job. Abandoned j ==> NUM_LE 3 (Attempts j)
    claim     !j:job. NUM_LT (Attempts j) 3 ==> ~(Abandoned j)

`Attempts` needs no interpretation here and cannot use one. Its **result type is already `num`**.
`Attempts j` is a term of the foundation's own type whose value nobody knows, which is not an atom
standing in for a number: it is a number, unknown. Nothing has to be approximated, and the claim is
settled by one fact that holds for **every** value it could take.

Three measurements, on `7dd2159`, decide the shape:

1. **The bridge exists and is a theorem of the library.** `Find NUM_LT_NOT_LE` answers
   `Peano.NUM_LT_NOT_LE : !x:num. !y:num. x < y ==> ~(y <= x)`. At `x := Attempts j` and `y := 3`
   it is exactly what the claim is missing, and it is obtained by specialisation rather than by any
   procedure reasoning about `Attempts`.

2. **With that instance, the skeleton is already intuitionistic and free.** Writing the shape out,
   `Ask (q ==> r) /\ (p ==> ~r) ==> (p ==> ~q)` answers *Proved, 266 inferences over **0** axioms*.
   So the logical half of the repair costs nothing, and `docs/adr/0022`'s guarantee survives the
   arrival of arithmetic intact.

3. **No search reaches the bridge, and this is the part that decided the mechanism.**
   `Ask !x:num. !y:num. x < y ==> ~(y <= x)` — the library lemma *verbatim* — answers
   *Unsettled: no proof: restate it as an inequality, an equation between reals, a denial of one,
   or a conjunction*. That is `Linarith`'s refusal: it recognises the shape and has no reading of
   `num`, and per the repository's rule about refusals the procedure that recognised the shape is
   the one whose refusal is reported. The instance `!x:num. x < 3 ==> ~(3 <= x)` is refused the
   same way.

## Decision

**A domain claim may mention the foundation's constants. The terms of foundation type in it stay
opaque, and the arithmetic it needs arrives as library lemmas the caller names, specialised at
those opaque terms.** An interpretation of a domain constant is a separate capability, is not on
the path to this one, and is not built here.

Concretely, three things and their limits.

**Foundation constants are permitted, and opaqueness is what makes that safe.** A subterm of
foundation type built from the domain's constants — `Attempts j` — is neither interpreted nor
approximated. It is a variable of that type as far as every step is concerned, so a fact used about
it must hold for all of its values, and a conclusion drawn is a conclusion about every job there
could be. The failure the old refusal prevented, an atom standing in for a number, cannot occur,
because nothing substitutes anything.

**The bridging facts are named by the caller, not found.** `settle` gains a set of library lemma
names; each is specialised at the claim's own foundation-typed subterms and joins the domain's
axiom instances in the same irredundant-core cut-down. Nothing searches, nothing ranks, nothing
guesses. A caller who names a lemma that does not apply gets it dropped by the cut-down, at the
cost of the decisions it takes, not a wrong answer.

**The accounting reports the arithmetic honestly, and this is what the method is for.** A bridging
lemma carries whatever its own derivation spent, and `Derivation.axiomsOf` already walks that. So a
release-gate conclusion that reached for `NUM_LT_NOT_LE` will report the naturals' two foundational
axioms, choice and infinity, where the purely propositional conclusion reports none. That is a
real change in what the reader is being asked to accept and it must show: **the promise is not that
arithmetic is free, it is that arithmetic is visible.** `Domain.Spending` already splits the
domain's assumptions from the foundation's, so no new reporting is invented; what is new is that
the foundational column can now be non-empty for an honest reason rather than only through
`Propositional` reaching for `SELECT`.

**The refusal narrows rather than disappears.** It still fires, and now says something sharper: a
claim is refused when it needs a fact about a domain **type** that the foundation cannot state.
`Cost` declared as a type operator with `cheap : Cost -> bool` has no arithmetic content, and
asking whether a cost is at most three is a question about what `Cost` means. That is the case the
card's interpretation map is for, and it stays refused.

## Consequences

`Domain.Built.settle` takes an extra argument and the existing call sites keep their behaviour with
an empty set, so `docs/adr/0022`'s route is untouched for a claim with no arithmetic in it.

`DomainTheorySpec`'s refusal test changes subject rather than being deleted. It asserted that
`NUM_LT` is refused; what it asserts now is the pair: the same claim **derived**, naming the bridge,
with the accounting showing one domain axiom and the naturals' two; and a claim about a domain type
with no foundation meaning still refused by name. Deleting the refusal test and keeping only the
derivation would leave the narrowed refusal unguarded, which is the shape this repository loses
most.

The bound on instances gets tighter for the same work. The cut-down costs `2n + 1` decisions and
`n` now counts the bridges too, so a caller naming six lemmas on a four-axiom domain pays twenty-one
decisions rather than nine.

## Alternatives rejected

**An interpretation map from a domain constant to a term of the chain, done first.** This is the
card's own plan and the ordering it insisted on: no lifting of the refusal without a meaning. It is
rejected as the *next* step, not as a capability. Measured against the example the card itself names
as the acceptance criterion, the interpretation has nothing to interpret: `Attempts` already returns
a `num`, and a map sending it to some other term would be inventing a claim about jobs that nobody
asserted. Building it first would mean building the machinery for a case the criterion does not
contain, and leaving the criterion unmet behind it. It remains the right answer for a domain
**type** that must carry arithmetic, and that is where it will be built.

**Handing the whole claim to `Linarith` with the domain's constants abstracted to variables.** It
looks like the smaller change and it does not work here, which measurement 3 shows: `Linarith`
decides a fragment of the **reals**, and `NUM_LT` over `num` is outside it. A claim about counted
things is about `num`, so this route would answer none of the criteria that motivated the work. It
also fails the accounting test in a way that is easy to miss: `Linarith` certifies, so its
foundational cost would be reported, but nothing would report that a bridging step had happened at
all, and the reader would see the axioms without the reason.

**Searching the library for the bridge instead of taking a name.** This is where the work goes next
and it is not taken now, for the reason the repository already gives about tactics: a procedure
that guessed would be worse than one that stops, and a search that reaches a conclusion by a route
the reader cannot see defeats the one thing this tool is for. A search here is also not the general
one: it is bounded, its candidates are library lemmas about the foundation constants the claim
already mentions, and it must report which it used. That is a piece of work with its own criterion,
not a flag on this one.

**Leaving the refusal as it is.** Defensible and it is what the code did until today, on the honest
argument that refusing beats misleading. What it costs is measurable rather than theoretical: the
example in `DomainTheorySpec` is a rule about retries that the system can state, cannot settle, and
refuses for a reason that turns out not to apply to it.
