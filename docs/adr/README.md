# Decision records

**EXCERPT — for anyone scanning the index:**
One file per architectural decision, numbered, never deleted. This directory covers decisions
about the shape of the system, not about individual algorithms: if a choice can be reversed by
editing one function, it belongs in a comment at that function instead. The index below is the
only place supersessions are annotated, so it tells you which decisions are live without opening
anything.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

A record is **superseded**, not edited and not removed. Editing loses the reason the first
decision was made, which is exactly what is needed to judge whether the new context really
differs. Deleting breaks every citation, and a citation resolving to nothing is worse than an
outdated one.

Several of these reject an option that is genuinely attractive. That is the function of the
directory: a decision with no written alternative gets re-litigated by the next person who finds
the rejected option attractive, and they will.

## Index

| # | Title | Status |
|---|---|---|
| [0001](0001-higher-order-logic-not-first-order.md) | Higher-order logic, not first-order | accepted |
| [0002](0002-locally-nameless-binders.md) | Locally nameless representation for binders | accepted |
| [0003](0003-trust-boundary-is-the-module-graph.md) | The trust boundary is the module graph | accepted |
| [0004](0004-reals-axiomatised-not-constructed.md) | The reals are axiomatised, not constructed | accepted, revised by 0007 |
| [0005](0005-a-model-is-untrusted-and-answers-only-at-a-point.md) | A model is untrusted, and answers only at a point | accepted |
| [0006](0006-a-type-is-defined-by-a-bijection-with-a-subset.md) | A type is defined by a bijection with a subset of an existing one | accepted |
| [0007](0007-the-reals-are-constructed.md) | The reals are constructed, and the foundation gains the classical axioms | accepted, extended by 0016 |
| [0008](0008-a-constant-carries-what-defined-it.md) | A constant carries the term that defined it | accepted for a DEFINED constant, revised by 0019 for a declared one |
| [0009](0009-the-classical-axioms-and-a-reason-that-was-wrong.md) | The classical axioms, and a reason that was wrong | accepted |
| [0010](0010-no-computing-rule-in-the-kernel.md) | No computing rule in the kernel | accepted |
| [0011](0011-the-numeric-screen-has-two-stages.md) | The numeric screen has two stages, and the second is arbitrary precision | accepted |
| [0012](0012-a-numeral-belongs-to-the-type-its-context-forces.md) | A numeral belongs to the type its context forces | accepted |
| [0013](0013-the-embedded-theory-is-pa-and-the-coding-is-the-beta-function.md) | The embedded theory is PA, and the coding is the beta function | accepted |
| [0014](0014-the-object-syntax-is-a-number-and-a-pair-is-not-a-sequence.md) | The object syntax is a number, and a pair is not a sequence | accepted |
| [0015](0015-the-project-is-called-symbolum.md) | The project is called Symbolum | accepted |
| [0016](0016-what-the-construction-needs-in-front-of-it.md) | What the construction of the reals needs in front of it, and what does not wait for it | accepted, extends 0007, one open question settled by 0018 |
| [0017](0017-the-transcendental-functions-are-their-power-series.md) | The transcendental functions are their power series | accepted |
| [0018](0018-an-operator-symbol-stands-for-more-than-one-constant.md) | An operator symbol stands for more than one constant, and the elaborator picks which | accepted, settles an open question of 0016 |
| [0019](0019-a-declared-constant-still-has-no-origin-and-here-is-what-that-costs.md) | A declared constant still has no origin, and here is what that costs | accepted, revises 0008 |
| [0020](0020-an-inductive-set-is-the-intersection-and-is-polymorphic.md) | An inductively defined set is the intersection of the closed sets, and it is polymorphic | accepted |
| [0021](0021-the-derived-connectives-are-constants-that-build-codes.md) | The derived connectives are constants that build codes | accepted, spends 0014 |
| [0022](0022-the-intuitionistic-fragment-gets-its-own-decision.md) | The intuitionistic propositional fragment gets its own decision procedure | accepted, spends 0009 |
| [0023](0023-the-propositional-address-is-served-by-the-calculus.md) | The propositional address is served by the calculus, and the gate is the address | accepted, extends 0022 |
| [0024](0024-a-domain-claim-reaches-arithmetic-through-named-bridges.md) | A domain claim reaches arithmetic through named bridges, not through an interpretation | accepted, extends 0022, extended by 0027 |
| [0025](0025-a-goals-own-hypotheses-are-facts.md) | A goal's own hypotheses are facts, and the deduction theorem is what pays for them | accepted |
| [0026](0026-an-exhausted-free-route-is-reported-not-hidden.md) | A free route that ran out of net is reported, not hidden behind the price it fell to | accepted, extends 0022 |
| [0027](0027-the-bridge-is-searched-for-above-the-method-that-spends-it.md) | The bridge is searched for above the method that spends it, one candidate at a time | accepted, extends 0024 |
