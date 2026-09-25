# 0019. A declared constant still has no origin, and here is what that costs

- **Status:** accepted, revises `docs/adr/0008`
- **Date:** 2026-09-16

Revises `docs/adr/0008`, which decided the identity of a **defined** constant and deferred the
identity of a **declared** one while reading as though it had settled both.

## Context

`0008` decided that a constant carries the term that gives it its identity, and that two constants
are the same when they have the same name, the same type and the same origin. It then wrote:

> A declared constant has no origin, which is right: an uninterpreted name says nothing, so two
> theories declaring one are talking about the same thing.

That sentence is true of a constant that is merely declared. It is not true of one that is declared
**and then constrained by an axiom**, which is what every primitive of the reals is. `real_zero`,
`real_one`, `real_add`, `real_mul`, `neg`, `inv` and `real_lt` are declared by `Real.Declarations`
and pinned by the sixteen axioms; `Theory.declareConstant` writes nothing into `origins`;
`Theory.constant` hands back `Const(name, instance, origins.get(name))`, so all seven carry `None`;
and `Const.sameOrigin` matches `(None, None)`. Two theories that declare one name and axiomatise it
in opposite directions therefore produce constants that compare **equal**.

`SoundnessAttackSpec` derives `|- F` from exactly that, with no hypothesis, from two theories each
declaring `p : bool`. It is archived as a **limit** rather than as a must-refuse, and correctly so:
the repair is this decision and not a missing check. In ordinary use there is one theory of the
reals and the case does not arise.

**What changed, and it is the reason to reopen rather than to restate.** The deferred decision now
blocks a second thing. `docs/architecture.md` line 255:

> Making the invariant true in general means a theorem knowing the theory it came from, which is
> the decision `docs/adr/0008` deferred for declared constants.

So the lineage of a theorem and the identity of an axiomatised constant are one question, and the
cost of leaving it open grows with the number of places that meet it. Today that is two:
multi-domain theories, which is the project's declared purpose, and theorem lineage.

`a9b78674` measured the hole, documented it, declared itself an analysis card and stopped, deferring
the decision to an ADR revising `0008`. **That ADR was never written**, and nothing carried it. This
is it.

## The three answers, and what measuring them cost

`a9b78674` posed three. Both of the substantive ones had a figure attached that nobody had rechecked,
and rechecking is what this record is for.

**1. The axioms naming a constant enter its identity.** Precise, and non-monotone: adding an axiom
that names a constant changes the constant and invalidates every theorem already proved about it.
`a9b78674` called that "probably the defect that excludes it" and left it deduced rather than
measured.

Measured, by partitioning `docs/lemmas.md` by development: **158 statements name one of the seven
declared-and-axiomatised constants of the reals** — 141 across the ten developments stated over the
reals, plus 17 in `Peano` naming `real_of_num`. The count is at `951efde` and is quoted as a count
rather than as a share on purpose: the denominator moves whenever anybody lands a lemma, so a
percentage falls as polymorphic work arrives and reads as the risk receding when the blast radius has
not moved at all.

**It is a lower bound**, and the reason matters: the count is over statements, and a theorem about
`num` proved through the embedding names a real constant in its derivation without showing one in its
statement.

The concrete case `a9b78674` asked about is `docs/adr/0007`, where the sixteen become theorems. Under
this answer that is not a refinement of the reals. It re-identifies all seven constants at once and
invalidates every one of those 158 together.

**2. A lineage identity on the theory, generated at extension and propagated.** This is Isabelle's
design. `0008` rejected it on cost: `refl`, `assume` and `beta` would have to take a theory or a term
certified against one, "which is about 240 call sites", and `refl` would stop being total.

That number is from 2026-09-10. Remeasured today:

| | `Kernel.refl` | `Kernel.assume` | `Kernel.beta` | total |
|---|---|---|---|---|
| `86641a7`, 2026-09-10, where "about 240" was written | 68 | 171 | 7 | **246** |
| `70648f0`, 2026-09-16 | 81 | 905 | 11 | **997** |

Comments stripped, `modules/*/src` including tests. **4.05 times.**

The first row is the point of the table. Running the criterion at the commit where the original
figure was written returns 246 against their "about 240", which is what licenses comparing the two;
without it a fourfold change and two people counting different things are the same observation.

So the rejection was not stale in the direction that would reopen it. **Rechecking made the rejected
option four times worse than when it was rejected**, and almost all of the growth is `Kernel.assume`,
which is what a repository of hand derivations is made of.

**3. An explicit check at the boundary.** Closes nothing by itself. It is the only one of the three
that is not a change to the kernel's rules, and therefore the only one available while the other two
are being weighed.

**And it was already built when this record listed it as an option**, which is the one thing here
that was carried forward without being rechecked. `a9b78674` posed the three on 2026-09-12;
`Derivation.foreignTo` landed on 2026-09-13 and is this answer, with a production caller in
`Session` and the case that motivates it asserted in `SoundnessAttackSpec` and `DomainTheorySpec`.
Both of the figures this record inherited were rechecked and one moved by a factor of four; the
option list was not, and its third entry had stopped being an option and become a fact. Written
down rather than quietly corrected, because it is the same failure the rest of this record is
about: a sentence true on the day it was written, read later as though it still were.

## Decision

**`0008`'s rule stands unchanged: a declared constant has no origin.** Not because the objection to it
is answered — it is not — but because both alternatives are now measured to be worse than when `0008`
weighed them, one of them four times worse and the other by a third of the library.

**And `0008` is revised in what it claims rather than in what it does.** It reads as though the
identity question were closed. It is closed for a defined constant and open for an axiomatised one,
the open half is the half a theory is made of, and this record is the one that says so in
`docs/adr/`, where a reader looking for the answer will go. The sentence in `architecture.md` that
said the opposite was in another file.

**The residual risk is named rather than removed, and the name is `Derivation.foreignTo`.** It does
not make the falsity underivable; it makes the crossing nameable at the one place a caller can act
on it, and it changes no inference rule, so it costs nothing that the table above prices.

This record first wrote that check as `Theory.certifies(thm)`, a method on `Theory`. That spelling
is **withdrawn rather than scheduled**, on two measurements taken on 2026-09-16.

The first is that it would be a second name for something that already works, which is a defect
while the two agree.

The second is placement, and it is the stronger of the two. What `Theory.certifies` was specified to
compare over a term — name, type and origin — is `Theory.checkTerm`, which is public and which all
three theory extensions already call. What decides **this** case is the other half: the axioms a
theorem rests on against the axioms a theory holds, and an axiom is held by the theory rather than
by any constant, which is why no field on a term could carry it. Run over the falsity two declaring
theories produce, the vocabulary half alone answers **yes** against each of the two theories that
built it, because `p` does not occur in `|- F`; `SoundnessAttackSpec` asserts that outcome rather
than describing it, beside the axiom half answering no to both.

So a method on `Theory` would have put the check inside the trusted base, for something that must
not be trusted. `DocumentationSpec` bounds that base at 1220 lines, 1200 when this was decided, and measures it over **the four
files a defect in which can produce a false theorem**, which is not the same as the directory:
`Kernel.scala`, `Term.scala`, `Theory.scala` and `Type.scala`. `Derivation.scala` is one of the four
that are out, classified as record and display, and the classification is checked rather than
asserted — the spec reads each of those files for `new Thm(` and fails if it finds one. So the
argument for excluding it is the same argument that makes it the right home for this check: a wrong
answer from a record is a false alarm and never a false theorem.

`Theory.scala` is in. The card's own constraint said to measure before and after, and nobody had.
Measured at `fb3f45a`: the four come to **1184 lines against the bound of 1200**, so the headroom is
sixteen and a method of this repository's comment density does not fit in it. Nor does moving the
check to a new file in that directory buy the room, which is worth saying because it is the obvious
escape: a second assertion pins the directory's contents to the union of the two lists, so a file
nobody has classified fails that one instead. The bound had never moved when this was decided —
raised to 1400 once, on 2026-09-10, and put back the same day, and the two records that spent
against it deliberately, `0006` for the type definition rule and `0008` for the identity on
constants, spent lines rather than raising it. It has moved once since, in `0047`, which raised it
to 1220 for the citation rule. Paying for this check means a third such record, which is a cost the table above
says option 3 does not have.

**This decision is not deferred again.** The lesson of how this record came to be needed is that a
card closed by deferring a decision loses it unless the deferral leaves on a card of its own. That
card is `c776f787`, and what it returned is the correction above: the check existed three days
before this record listed it as an option. What it delivered instead of a second implementation is
the pair of assertions the boundary claim needed and did not have — that the falsity is foreign to
**both** of the theories that produced it, where the test that carried that sentence in its name
measured one of them and the base, and that a check reading only the vocabulary takes it.

## Consequences

**`SoundnessAttackSpec` keeps deriving `|- F` and stays archived as a limit.** Nothing here makes it
refuse. What changes is that the limit now has a record that states the measured cost of each way out
instead of an intention to decide later.

**"A domain theory sits beside the chain and must stay there" stays load-bearing.** It is what keeps
the two-theory case out of ordinary use, and it is the only thing that makes it **impossible**:
`Derivation.foreignTo` makes the crossing detectable to a caller that asks, and nothing forces a
caller to ask.

**The multi-domain card is unblocked in the sense that matters and not in the sense that was hoped.**
`23045598` says nothing is to be built before this decision is made. It is made. It is not made in
its favour: two theories that axiomatise one name still produce constants that compare equal, so a
multi-domain surface has to keep domain theories apart by construction rather than rely on the kernel
to refuse a mixture. That is a design constraint on that card, stated here so it is not discovered
there.

**`docs/adr/0007` gains a line of work.** When the sixteen become theorems the seven constants stop
being axiomatised and start being defined, which closes this hole for the reals specifically, by
construction rather than by decision. That is a reason to want 0007 and not a reason to wait for it:
it fixes one theory and says nothing about a domain's.

## Alternatives rejected

**Deciding for option 1 on the ground that non-monotonicity is rare.** Measured at 158 statements at
`951efde` and rising with every lemma, and the one concrete change anybody has planned — `0007` —
triggers it on all seven constants at once. Rare is not the measurement; the measurement is that the
one scheduled event is the worst case.

**Deciding for option 2 on the ground that the cost was overstated.** It was understated. 246 then,
997 now, by the same criterion run at both commits.

**Deferring again, quietly.** That is how this record came to be needed, and `a9b78674` is the
evidence: a card that defers a decision and closes itself leaves nothing carrying it. Where a
deferral is right, it goes on a card.
