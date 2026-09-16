# 0008. A constant carries the term that defined it

- **Status:** accepted for a **defined** constant; **revised by `0019`** for a declared one
- **Date:** 2026-09-10

**What this record settles and what it does not.** The identity below is the identity of a constant
that a definition gives a body to. A constant that is **declared and then axiomatised** — which is
every primitive of the reals — gets `None` here, and two theories that declare one name and
axiomatise it in opposite directions produce constants that compare equal. This record reads as
though it had closed that; it had not, and `docs/adr/0019` is where the measured cost of each way
out is written down.

## Context

`Kernel`'s own documentation has said since it was written that a theorem does not record the
theory it was proved against, that two theories defining one name differently are each consistent
while a development mixing their theorems is not, and that nothing detects it. On 2026-09-10 that
paragraph stopped being a caveat and became a derivation:

```scala
val asTruth   = Kernel.defineConstant(logic.theory, "c", logic.truth)._2    // |- c = T
val asFalsity = Kernel.defineConstant(logic.theory, "c", logic.falsity)._2  // |- c = F
Conv.sym(asTruth).flatMap(Conv.trans(_, asFalsity))                         // |- T = F
```

Both halves are theorems the kernel was right to produce. Each extension is conservative, each
theory is consistent, and `defineConstant` refuses a repeated name only within one theory.
`SoundnessAttackSpec` runs it.

**What changed is not the hole but the traffic.** The same paragraph declined to close it because a
lineage costs a field on every theorem to prevent an error nobody had made. On 2026-09-10 the
naturals arrived as a development beside the reals rather than over them, two chains from one root,
and within hours a session asked whether the two could be used together and tried to stack them.
That is the error, arriving.

Three measurements bound the work, taken rather than recalled:

- **A constant is built in two places**, `Theory.constant` and `Term.equalityAt`, and rebuilt in
  one, `Term.substituteTypes`. The constructor is `private[kernel]`, so there is nowhere else.
- **Pattern matches on `Const` are everywhere**, across all four modules, and every one of them
  reads the name and the type. None reads a third field, because there is none.
- **The three rules that admit a term from outside** are `refl`, `assume` and `beta`, and they have
  about 240 call sites between them. That number is what the alternative below costs.

## Decision

A constant carries the term that gives it its identity. Two constants are the same constant when
they have the same name, the same type, **and the same origin**.

- `defineConstant` gives its constant the definition body.
- `defineType` gives `abs` and `rep` the predicate the type was carved out by.
- A declared constant has no origin, which is right: an uninterpreted name says nothing, so two
  theories declaring one are talking about the same thing.

`Theory` records the origins beside the definitions, and `Theory.constant` hands them out, so a term
built against a theory carries them without any call site changing. `Theory.checkTerm` compares
them, so the three operations that extend a theory refuse a term whose constant is not theirs even
when the name and the type agree.

`Const` stops being a case class and keeps a two-field extractor, so every pattern match in the
system goes on reading the name and the type and ignoring the origin, which is what they all want.
Equality, hashing and the total order include it.

## Consequences

**The falsity above stops being derivable, and by refusal rather than by check.** The two `c`s are
different terms, so `trans` reports that its two sides differ and names both. No rule was changed to
make that happen: the comparison is the `==` the kernel already performs at every step.

**A theorem about a declared constant no longer combines with one about a constant of the same name
defined elsewhere.** That is a valid inference this now refuses, since a theorem about an
uninterpreted constant holds under every interpretation including that definition. Conservative in
the safe direction, and stated here because a caller who meets it will want to know it is deliberate.

**Two constants that differ only in origin print alike.** This system is careful about that shape
elsewhere, so it is worth being exact: it can only arise between two chains, the refusal names both
terms, and inside one chain there is one origin per name. It is the cost of the identity being
structural rather than a name.

**One field per constant, compared on every term comparison.** The two origins are the same object
in the common case, so equality settles it by reference; the structural comparison runs only when
two chains actually meet, which is the case this exists for.

**The kernel grows.** Measured after the fact and reported in the commit, against the 1200-line
bound `DocumentationSpec` asserts.

## Alternatives rejected

**A theory certificate on every theorem, checked at every binary rule.** This is Isabelle's design
and it is correct. It costs what the third measurement says: `refl`, `assume` and `beta` would have
to take a theory or a term certified against one, which is about 240 call sites, `refl` would stop
being total and start returning a refusal, and every binary rule would gain a check that today's
`==` performs for free. It also puts the theory back into every inference, which
`Theory`'s own documentation gives as the reason theories are values here rather than one global
signature. Rejected on cost against an equal outcome, not on correctness.

**A hash of the definition as the identity.** Cheap, and a collision is a soundness hole. A trusted
base does not get to assume a hash function.

**A globally unique stamp per definition, from a counter.** Correct and non-deterministic: two runs
of the same construction would produce terms that are not equal, and the tests, the ledger's keys
and every pinned printed form depend on two runs agreeing.

**Leave it, and rely on building one chain rather than two.** It is what the previous paragraph in
`Kernel` proposed, and `Real.construct`, `Natural.construct` and `Classical.construct` were changed
the same day to make one chain possible. That is worth having and it is not a closure: it makes the
safe thing available, and nothing stops the other. A kernel that relies on its callers arranging
themselves correctly has moved the guarantee out of the kernel.

**Refuse the second definition globally.** `defineConstant` could refuse a name that any theory has
defined, which needs a global registry, which is the mutable global signature this design gave up
for a reason.
