# 0006. A type is defined by a bijection with a subset of an existing one

- **Status:** accepted
- **Date:** 2026-09-09

## Context

The kernel can declare a type operator and it cannot define one. `Theory.declareTypeOperator`
adds a name with an arity and says nothing about what inhabits it, which is why declaring costs
nothing to believe: an uninterpreted name proves exactly what its absence proves, and
`docs/proving.md` says so under "a declared type cannot be said to be inhabited". `?x:agent. T`
is not derivable and asserting it would be an axiom.

That is the whole of the problem. Every new type must currently arrive as an axiom, so the
naturals must arrive as axioms, and with them induction, recursion, finite sums, sequences, and
every function this system would rather define than assume. The first row of
`docs/evaluation.md` scores zero on miniF2F, PutnamBench and ProofNet for one reason and it is
this one: the goals cannot be **written down**. No Collatz statement can be written either,
which is what the owner wants the system for.

Sixteen axioms is the number `RealSpec` asserts and `CLAUDE.md` publishes. Adding the naturals
as axioms would move it, and would move it by an amount nobody can bound in advance, because
each further construction wants more. A rule that defines a type instead adds nothing to the
axioms at all, and that is the difference this record exists to fix in place.

Three measurements bound the work:

- **The trusted base is 999 lines of a 1200-line budget**, which `DocumentationSpec` asserts
  through `TrustedBaseLineBound` and `docs/architecture.md` publishes. The rule, its refusals and
  its documentation have 201 lines to fit in. That is enough and it is not generous; if it turns
  out not to be, the budget is raised deliberately and with a reason written down, never quietly.
- **The kernel knows equality and nothing else.** `Term.EqualityName` is its only built-in
  constant and `Type.Bool` its only built-in type. The connectives, including the existential, are
  definitional extensions in `modules/logic`, which sits above the kernel. So the rule cannot ask
  for `|- ?x. P x`: it has to take the witness form.
- **The precedent is `Kernel.defineConstant`**, which already does the analogous job for a
  constant: it checks the definition is closed, checks no type variable escapes, extends the
  theory, and returns the theory alongside the defining theorem. The type rule has the same shape
  and the same return convention.

## Decision

Transcribe HOL Light's `new_basic_type_definition` from Harrison's account and from `fusion.ml`,
as a third theory extension beside `defineConstant` and `assertAxiom` rather than as an eleventh
inference rule. The ten inference rules stay ten: this one takes a theory and returns a theory, and
belongs with the other two that do.

Given a predicate `P : A -> bool` and a theorem `|- P w` that something satisfies it, the rule
introduces a type operator whose arity is the number of type variables in `P`, two constants
`abs` and `rep` mapping between the new type and `A`, and returns the two theorems that say they
are a bijection onto `P`'s extension:

```
|- abs (rep a) = a
|- P r <=> rep (abs r) = r
```

Nothing is asserted. The new type is inhabited because a witness was supplied, and the two
theorems are the definition of the abstraction rather than assumptions about it. The axiom count
does not move, and `RealSpec`'s assertion that the theory holds exactly sixteen is expected to
keep passing unchanged.

**The signature takes a witness theorem, not an existential**, for the reason in the context: the
kernel has no `?`. A caller holding `|- ?x. P x` in the logic layer eliminates it there and hands
the witness down, which is where that reasoning belongs.

**Who wrote it, and the constraint that was waived.** The card asking for this rule said a model may
be a second reader of the finished diff and may write adversarial cases, but must not be the author.
The argument for that is good and is worth keeping on the record: the kernel hole closed on
2026-09-03, an open term escaping through the extractor for `Abs`, survived `docs/architecture.md`,
`TrustBoundarySpec`, `IsolationSpec` and 251 tests. Reading is what catches that class of defect and
writing is not, so the scarce resource is a careful reading of Harrison against a careful reading of
the diff, and a model that produces the transcription has the author reading its output instead of
the source.

The constraint was put back to the owner and waived. This transcription was written by a model on
2026-09-10, so what is missing is the second reading and not the first. That is a real debt, and it
is recorded here rather than in a commit message because whoever next audits the trusted base needs
to know which of its parts has been read by two people and which by one. Item 7 of the build order
in `docs/evaluation.md` says it against the item that asked for the constraint, and sends a reader
back here for the detail.

**The second reading, and what it found.** Done later on 2026-09-10 by a session of the same model
that wrote the rule, which is not the reading the paragraph above asks for: it reduces the debt and
does not close it, and a person still has not read this rule against Harrison. What it found is one
thing, and it is the shape a second reading is for rather than a mis-transcription. The rule did not
check that the witness was a theorem of the theory it was extending. `defineConstant` and
`assertAxiom` both call `Theory.checkTerm` on the term they take in and this rule did not, so a
predicate naming a constant the theory does not declare defined a type whose characterising theorem
that same theory then refused as an axiom. Upstream has no analogue of the check and there was none
to transcribe: HOL Light has one global theory, so a theorem's constants are in the signature by
construction, while here a `Theory` is a value and `Theory.checkTerm`'s own comment says a term "can
be built against one theory and handed to another". Measured rather than argued, then fixed with the
check and a case in `TypeDefinitionSpec`. No falsehood was derived from it and none is claimed: what
was broken is the invariant that a theorem of a theory names only that theory's signature.

Everything else in the transcription was checked line against line and is faithful, including the
one thing that would be easy to get wrong quietly: the arity is read through `Term.typeVariables`,
which walks the type of every subterm rather than only the predicate's own type, and a version doing
the latter would let a type variable escape. One divergence from upstream is now written down where
the code is: HOL Light refuses the constant names before declaring the type operator, because
`new_type` mutates a global, and here the order is free because a failed step discards the theory it
would have returned.

## Consequences

**The axioms stay at sixteen and the roadmap unblocks.** The naturals become a definable type
rather than an assumed one, and after them induction, recursion, finite sums, sequences, and
trigonometric and exponential functions defined rather than assumed. `docs/evaluation.md` calls
this the first point at which the discovery loop screens inside a fragment with no decision
procedure, where numerical evidence carries information.

**The trusted base grows, and this is the cost.** Everything anyone is asked to believe grows by
the length of the rule. That is the right trade against the alternatives below, and it is a real
cost rather than a formality: a defect here is silent, permanent and retroactive, and would make
every theorem the system has ever produced worth nothing.

**The line budget tightens from 201 lines of headroom to 94.** Measured after the fact: the kernel
went from 999 lines to 1106 against a bound of 1200, so the rule, its two refusals and its comment
cost 107. The next thing that wants room in the kernel meets a much smaller budget, which is
intended: a trusted base one can read in a sitting is the property the number exists to protect.
The signature check the second reading added took it to 1124, so the headroom is 76.

**A type operator's arity becomes derived rather than given.** It is the count of `P`'s type
variables in a fixed order, so a caller cannot choose it, and a predicate whose type variables
change changes the arity of the type it defines. That is a sharper edge than `declareTypeOperator`
has and it belongs in the rule's documentation.

**Two more names enter the theory per definition.** `abs` and `rep` are ordinary constants and
collide with ordinary constants, so a definition can fail for a reason that has nothing to do with
types.

## Alternatives rejected

**Assert the naturals as axioms.** The cheapest thing that would work, and it is what a system in
a hurry does. Rejected because it moves the number the whole design is organised around: sixteen
axioms is what `CLAUDE.md` publishes, `RealSpec` asserts and `docs/adr/0004` argues for, and the
argument in 0004 was explicitly that the *reals* are a complete ordered field with a categorical
axiomatisation, which the naturals within a higher-order logic are not — they are definable, and
defining them is the ordinary thing to do. Asserting them would also not stop: every construction
after them would want its own axioms, and the count would grow by an amount nobody could bound in
advance.

**Add a general axiom-of-infinity and build the naturals from it.** Closer to honest, and it is
what HOL Light itself does *after* it has the type definition rule. Rejected as an alternative
because it is not one: infinity is asserted about a type, and there is no type to assert it about
until a type can be defined. It is the step after this one, not instead of it.

**Take type definition as a derived rule over `declareTypeOperator` plus axioms.** Declare the
operator, then assert the two bijection theorems as axioms about it. It produces the same
theorems and needs no kernel change at all. Rejected because it is the first alternative wearing a
disguise: the two theorems would be axioms, they would appear in `Theory.axioms`, the count would
move by two per type defined, and nothing would check that the predicate has a witness — so a
definition over an empty predicate would assert a bijection with nothing and make the theory
inconsistent. The check *is* the rule.

**Design a rule of our own rather than transcribing one.** Tempting because HOL Light's is
shaped by OCaml and by its own conventions, and a rule written for this kernel would fit its
idiom. Rejected on the same argument as the reading above: `new_basic_type_definition` has been
under adversarial reading for thirty years by people looking for exactly the defect this file is
about, and a rule that is merely equivalent-looking has been read by nobody. Fitting the idiom is
worth nothing against that. Where the two disagree, HOL Light wins and the difference is written
down.

**Return one theorem instead of two.** The second, `P r <=> rep (abs r) = r`, is the one that
carries the predicate, and a rule returning only `abs (rep a) = a` would define a type isomorphic
to *something* without saying what. Rejected because it is not a simplification: it is the same
rule with the useful half removed.

## What the rule must refuse, and the tests that say so

Enumerated here because the card assigns this list to a second reader, and because a rule of this
kind is defined as much by what it turns away as by what it produces. Each row becomes a case in
`SoundnessAttackSpec` beside the existing ones.

| The attack | Why it must be refused | What a wrong answer would cost |
|---|---|---|
| A predicate with a free term variable, `\x. x < y` | The arity is read from `P`'s **type** variables, and a free term variable makes `P` a schema rather than a predicate. `defineConstant` refuses the same shape, for the reason its comment gives: a mistyped name parses as a variable and prints indistinguishably | A type defined per value of `y`, with one name |
| A witness theorem with hypotheses, `h |- P w` | The witness must hold outright. A hypothesis makes the inhabitation conditional, and the two theorems returned carry none, so the condition would be discharged into silence | A type asserted inhabited on an assumption nobody records |
| A witness theorem whose conclusion is not an application | There is nothing to read `P` and `w` off. `|- T` is the shape that arrives when a caller proves the wrong thing | Whatever the extractor happens to return from a term of another shape |
| A witness for a **different** predicate than the one named | The rule takes `P` from the theorem, not beside it, so this is the case that must be impossible by signature rather than by a check. A signature that takes both is the defect | A bijection with the extension of a predicate nobody proved inhabited |
| A type name already in the theory | `declareTypeOperator` refuses it, and the rule must not route around that | Two types of one name, and theorems about each that mix silently |
| Either of `abs`, `rep` already a constant | Same, through `declareConstant` | An existing constant's meaning replaced under theorems that already mention it |
| A type variable in the witness that is not in `P` | The arity comes from `P`. A term may carry type variables that its own type does not, so this is not ruled out by well-typedness, and what happens to them has to be a decision rather than an accident | Depends on the transcription; the point of the test is that the answer is pinned rather than discovered |
| The two returned theorems, re-derived through the ordinary rules | Not an attack but the must-accept half. A rule whose refusals are all correct and whose product is unusable passes every test above | A rule nobody can use, found late |

Two things this list is not. It is **not coverage**: it is the attacks that occurred to one
reader, and the 2026-09-03 defect is the standing evidence that a corpus of attacks proves only
what it contains. And it is not a substitute for the must-accept case above it: the rule has to
define a type somebody can then use, and the first thing to try it on is the naturals it exists
for.
