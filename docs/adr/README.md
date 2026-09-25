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

**A figure in a record is a photograph of the day it was decided**, for the same reason: it is what
was measured when the choice was made, and it stays true of that day when the code moves on. So
the counts, sizes and timings below are not kept current and a reader should not expect them to
be. The exception is a figure something live still rests on, which is usually the constant the
record decided: those are spelled from the code by a test, `FiguresSpec` and `DocumentationSpec`
hold the ones that are, and a record whose decided value moved says so by going red rather than by
being edited.

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
| [0023](0023-the-propositional-address-is-served-by-the-calculus.md) | The propositional address is served by the calculus, and the gate is the address | accepted, extends 0022, revised by 0031 |
| [0024](0024-a-domain-claim-reaches-arithmetic-through-named-bridges.md) | A domain claim reaches arithmetic through named bridges, not through an interpretation | accepted, extends 0022, extended by 0027 and 0028 |
| [0025](0025-a-goals-own-hypotheses-are-facts.md) | A goal's own hypotheses are facts, and the deduction theorem is what pays for them | accepted |
| [0026](0026-an-exhausted-free-route-is-reported-not-hidden.md) | A free route that ran out of net is reported, not hidden behind the price it fell to | accepted, extends 0022 |
| [0027](0027-the-bridge-is-searched-for-above-the-method-that-spends-it.md) | The bridge is searched for above the method that spends it, one candidate at a time | accepted, extends 0024 |
| [0028](0028-a-domain-type-is-interpreted-and-a-domain-constant-is-defined.md) | A domain's type is interpreted at the build, and a domain's constant is defined rather than declared | accepted, extends 0024 |
| [0029](0029-the-corpus-asks-for-arithmetic-and-not-for-saturation.md) | The corpus asks for arithmetic and not for saturation | accepted, spends 0025 |
| [0030](0030-the-matchers-fragment-is-not-extended-and-here-is-the-census.md) | The matcher's fragment is not extended, and the census is why | accepted |
| [0031](0031-a-price-a-bound-chose-is-not-a-price-the-claim-asked-for.md) | A price a bound chose is not a price the claim asked for | accepted, extends 0023 and 0026 |
| [0032](0032-the-certificate-gains-a-square-and-the-products-do-not-gain-a-degree.md) | The certificate gains a square, and the products do not gain a degree | accepted, spends 0029 |
| [0033](0033-the-integers-arrive-as-a-prerequisite-and-not-as-stage-four.md) | The integers arrive as a prerequisite, not as stage four of the construction | accepted, extends 0016 |
| [0034](0034-a-perturbation-harness-is-versioned-and-a-measurement-probe-is-not.md) | A perturbation harness is versioned and a measurement probe is not | accepted |
| [0035](0035-a-change-is-judged-by-what-it-covers.md) | A change is judged by what it covers, and the module average stays beside it | accepted |
| [0036](0036-a-rationals-denominator-is-a-successor.md) | A rational's denominator is a successor, so the carrier needs no carving | accepted, extends 0016 and 0033 |
| [0037](0037-the-rewriter-bounds-the-term-and-not-only-the-steps.md) | The rewriter bounds the term and not only the steps | accepted |
| [0038](0038-a-list-is-an-orientation-on-word-and-not-a-second-carrier.md) | A list is an orientation on `word` and not a second carrier | accepted |
| [0039](0039-the-fold-is-a-catamorphism-and-a-link-of-its-own.md) | The fold discards the tail, and is a link of its own | accepted, extends 0038 |
| [0041](0041-a-series-is-decided-against-closed-forms.md) | A series is decided against closed forms, and in both directions | accepted, extends 0017 and 0023 |
| [0042](0042-an-inductive-type-is-built-from-its-constructors-over-one-universe-of-trees.md) | An inductive type is built from its constructors, over one universe of labelled trees | accepted, extends 0006 and 0020 |
| [0043](0043-recursion-along-a-measure-asks-the-caller-for-admissibility.md) | Recursion along a measure asks the caller for admissibility, and is proved through the graph | accepted, extends 0042 |
