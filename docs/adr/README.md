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
| [0004](0004-reals-axiomatised-not-constructed.md) | The reals are axiomatised, not constructed | superseded by 0053, revised by 0007 |
| [0005](0005-a-model-is-untrusted-and-answers-only-at-a-point.md) | A model is untrusted, and answers only at a point | accepted |
| [0006](0006-a-type-is-defined-by-a-bijection-with-a-subset.md) | A type is defined by a bijection with a subset of an existing one | accepted |
| [0007](0007-the-reals-are-constructed.md) | The reals are constructed, and the foundation gains the classical axioms | accepted, extended by 0016, completed by 0053 |
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
| [0040](0040-a-representation-is-a-formula-whose-truth-is-the-predicate.md) | A representation is a formula whose truth is the predicate, and provability comes once | accepted, extends 0013 |
| [0041](0041-a-series-is-decided-against-closed-forms.md) | A series is decided against closed forms, and in both directions | accepted, extends 0017 and 0023 |
| [0042](0042-an-inductive-type-is-built-from-its-constructors-over-one-universe-of-trees.md) | An inductive type is built from its constructors, over one universe of labelled trees | accepted, extends 0006 and 0020 |
| [0043](0043-recursion-along-a-measure-asks-the-caller-for-admissibility.md) | Recursion along a measure asks the caller for admissibility, and is proved through the graph | accepted, extends 0042 |
| [0044](0044-a-refutation-is-named-and-not-numbered.md) | A refutation is named and not numbered, its size is its step count, and its width is a recursion | accepted |
| [0045](0045-a-polynomial-times-a-geometric-term-by-the-ratio-test-and-a-comparison.md) | A polynomial in the index times a geometric term: the ratio test at degree one, a comparison for each degree after it | accepted, extends 0041 |
| [0046](0046-identities-of-a-commutative-ring-are-decided-by-one-builder.md) | Identities of a commutative ring are decided by one builder, over constants and laws | accepted, extends 0036 |
| [0047](0047-a-report-stops-at-a-cited-fact-and-a-checker-does-not.md) | A report stops at a cited fact, and a checker does not | accepted, decides 0016's open choice |
| [0048](0048-a-width-lower-bound-is-stated-on-a-derived-clause.md) | A width lower bound is stated on a derived clause, and proved by critical assignments without a restriction | accepted, extends 0044; its sentence calling the constant better than asked is corrected by 0055 |
| [0049](0049-the-integral-is-a-gauge-integral-over-an-inductive-relation-of-fine-sums.md) | The integral is a gauge integral, over an inductive relation of fine sums | accepted |
| [0050](0050-the-licence-stays-gplv3-for-now.md) | The licence stays GPLv3 for now, and the question is answered rather than left open | superseded by 0068 |
| [0051](0051-sbt-2-with-test-as-the-whole-suite-and-jdk-21.md) | The build moves to sbt 2, `test` stays the whole suite, and the library asks for JDK 21 | accepted |
| [0052](0052-the-reals-are-lower-cuts-on-the-rationals.md) | The reals are lower cuts on the rationals, with the sign handled at multiplication | accepted |
| [0053](0053-the-sixteen-are-theorems-and-real-is-the-cut-type.md) | The sixteen are theorems: `real` is the type of the cuts, and its constants are aliases | accepted, completes 0007, supersedes 0004, extended by 0059 |
| [0054](0054-a-fractran-step-is-a-fold-into-bool-and-a-run-is-reach.md) | A FRACTRAN step is a fold into `bool`, and a run is `REACH` | accepted |
| [0055](0055-a-width-bound-that-says-something-is-on-an-expanding-graph.md) | A width bound that says something is on an expanding graph, and the one on the complete principle is a one-step argument | accepted, extends 0048 and corrects one sentence of it |
| [0056](0056-the-second-source-of-squares-is-a-gram-matrix-and-needs-no-search.md) | The second source of squares is a Gram matrix, and at degree two it needs no search | accepted, extends 0032 |
| [0057](0057-pi-is-twice-the-zero-of-cos-and-the-bounds-are-taylor-polynomials.md) | pi is twice the zero of cos, and the bounds that pin it are Taylor polynomials reached through the derivative | accepted |
| [0058](0058-one-instance-per-type.md) | One instance per type, because a chain spelt 808 types with 4.4 million objects | accepted |
| [0059](0059-the-sixteen-are-laws-and-axioms-are-what-a-theory-asserts.md) | The sixteen are laws: `axioms` names only what a theory asserts | accepted, extends 0053 |
| [0060](0060-complex-is-a-type-of-its-own-because-the-operators-are-shared.md) | `complex` is a type of its own over the pairs of reals, because the operators it shares are picked by type | accepted, extends 0018 |
| [0061](0061-the-fundamental-theorem-of-algebra-by-the-polar-route-with-a-lipschitz-bound-for-compactness.md) | The fundamental theorem of algebra by the polar route, with a Lipschitz bound standing in for compactness in the plane | accepted |
| [0062](0062-the-finite-fourier-inversion-and-the-collatz-iterate-over-characterising-equations.md) | The finite Fourier inversion, and the Collatz iterate as its instance over the equations that characterise the map | accepted |
| [0063](0063-finite-distributions-are-functions-on-an-initial-segment-and-the-value-of-an-experiment-divides-by-nothing.md) | Finite distributions are functions on an initial segment, and the value of an experiment divides by nothing | accepted |
| [0064](0064-rule-30-over-rows-and-as-a-map-on-the-naturals-with-the-walsh-inversion-and-a-bridge.md) | Rule 30 over rows and as a map on the naturals, with the Walsh inversion and a bridge between them | accepted |
| [0065](0065-gilbreaths-table-over-any-first-row-and-the-conjecture-as-a-condition-on-the-second-entry.md) | Gilbreath's table over any first row, and the conjecture as a condition on the second entry | accepted |
| [0066](0066-triangular-maps-on-the-naturals-as-a-hypothesis-with-rule-30-and-odd-affine-maps-as-instances.md) | Triangular maps on the naturals as a hypothesis, with Rule 30 and the odd affine maps as instances | accepted |
| [0067](0067-the-family-of-rules-l-xor-h-c-r-proved-once-with-rule-30-and-the-pascal-map-as-instances.md) | The family of rules `l XOR h(c, r)` proved once, with Rule 30 and the Pascal map as instances | accepted |
| [0068](0068-the-licence-is-agplv3.md) | The licence is the AGPLv3, so a network service built on this code owes its source too | accepted, supersedes 0050 |
| [0069](0069-one-instance-per-term.md) | One instance per term, because a chain held 13.2 million applications spelling 1.68 million | accepted |
| [0070](0070-a-proof-language-checked-by-the-kernel-and-written-without-scala.md) | A proof language, checked by the kernel and written without Scala | accepted |
