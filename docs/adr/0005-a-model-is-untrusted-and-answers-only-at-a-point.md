# 0005. A model is untrusted, and answers only at a point

- **Status:** accepted
- **Date:** 2026-09-04

## Context

The proof side had no way to be wrong cheaply. `Discovery` screens candidate identities numerically
before certifying them, but it screens `Expr`, whose variables carry values, and it certifies
`Term`, whose constants carry none. So everything stated in the logic was unscreenable: a claim
about a domain could only be proved or not proved, never refuted with a witness.

That gap has a second edge, and it is the one that matters more. A sequent `h1..hn |- c` carries its
undischarged premises, and that is the whole reason to prefer hypotheses to axioms: a theorem shows
what it rests on. But `h1..hn |- c` is **vacuously true when the premises contradict each other**,
and the kernel will produce `H |- c` and `H |- ~c` with equal correctness. Nothing in the repository
could notice. Over a domain of uninterpreted constants, where the premises are the contested part
and are written by hand one at a time, an inconsistent set is easy to produce and invisible to read.
The mechanism this repository leans on for domain reasoning was therefore unguarded at exactly the
place it is weakest, and the comparable systems have a finite model finder standing there.

## Decision

`modules/tactics` gains a `Model`, an `Evaluate` and a `Refutation`, all on the untrusted side, none
of them able to produce a `Thm`.

A **model** says what a theory's undefined constants denote and how many inhabitants each declared
type has. `Model.Reals` is the intended one: the seven constants the theory of the reals declares
and does not define, interpreted over `Double`.

An **evaluator** takes a term, a model and an assignment and returns what it denotes, or nothing.
Almost nothing is built in. The defined constants are unfolded from the equations the kernel proved
when they were introduced, so the model never restates what the theory already says.

A **search** answers a question about assignments: whether one falsifies an entailment, or whether
one satisfies a premise set. What it reports is the cases of `Refutation.Outcome`, and telling them
apart is the whole of the design rather than a convenience.

Four of them are this decision, of 2026-09-04, and each is a report on sampling: a witness `Found`;
`Survived`, no witness among the `n` points that answered; `NeverAsked`, **no point that answered at
all**; and `Undecided`, **a refusal**, when the premises force an equality between reals and sampling
therefore cannot settle anything. None of the last three may be read as any of the others.

Three more arrived on 2026-09-05 with the solving search and are recorded under the consequences
below rather than folded in here: `Solved`, the exact point, and `Contradictory`, no point at all,
for a premise set read as a linear system; and `NoCounterexample`, the same decision about the
premises taken together with the denied conclusion. They do not change this decision, since none of
them produces a theorem; what they change is which questions get an answer. They are decisions rather
than samples, which is one more distinction to keep and not one fewer.

## Consequences

The propose-and-check loop can be pointed at a claim rather than at an expression, and the answer
carries an assignment a person can inspect. `0 < x |- 1 < x` comes back with an `x` between the two,
which is a different kind of information from a tactic that could not prove something.

The consistency check exists, and it is the same search. `{x < y, y < z, z < x}` is a set nobody
reads as contradictory and the search finds no satisfying assignment in a hundred points, which is
the signal to look.

**Where that signal is not available, the search says so instead of producing it.** A premise set
containing `x = 1` is satisfied only at a point of measure zero, so sampling finds nothing and
`Survived` would mean the same thing there as it does for `{0 < x, x < 0}`, which is genuinely
contradictory. That is the shape of misleading answer this whole arrangement exists to avoid, so the
search refuses instead, by name, and names the premise. Only a positive occurrence counts: `~(x = 0)`
is `MUL_INVERSE`'s side condition and one of the commonest premises there is, and an equality that
has to be **false** is false almost everywhere, which is where a sampler already looks.

**Amended 2026-09-05: where the premises are linear, the search solves instead of sampling.** The
paragraph above stood for a day and was right about sampling and wrong about the scope of the
problem. A set of linear premises over the reals is a system, its satisfiability has a finite
certificate either way, and `Linarith` already held the machine that finds one; the same simplex
that weighs hypotheses for a proof finds a point that satisfies them, exactly, with rational
values. So `{x = 1}` comes back as `Solved` with the point rather than as a refusal, and
`{x < y, y < z, z < x}` comes back as `Contradictory`, which is a decision rather than a count of
failures.

That does not reverse this decision and does not move the trust boundary. The solver is on the
untrusted side with everything else that guesses; what it produces is a point or an assertion that
there is none, and neither is a theorem. What it changes is which questions get an answer at all,
and the answer to the one the paragraph below despaired of. The refusal stays for everything the
system cannot read as linear. The counterexample search is solved the same way, since an entailment
fails exactly where its premises hold and its conclusion does not, and over a total order the denial
of one inequality is another; a conclusion that is an equality is not denied, because its denial is
a disjunction and that is two systems rather than one.

The two decisions are named apart, and that is the same rule as everything else here: nothing
satisfying the premises is `Contradictory` and says the premises are worthless, while nothing
satisfying them together with the denied conclusion is `NoCounterexample` and says the claim is
good. One name for both would be the conflation this document is about.

The consequence was that this could not check the consistency of a premise set built from equations,
which is most of what a corpus of measurements and definitions is made of. That is the honest state
and it is what a solving search would lift.

**The solving route stops at the linear fragment, and the proof side does not.** That question was
left open when the search was made to solve, and the answer is an asymmetry rather than a limit that
more work removes. Since 2026-09-10 `LinearForm.of` multiplies a product of two unknowns out and
keys the result through `productAtom`, so the **proof** side reaches some product atoms: a
certificate weighs the hypotheses and adds them, the multipliers are non-negative except on an
equality, and the ring step checks the sum against the goal. Nothing is proved about an atom, so the
step is sound whatever the atom denotes. A **witness** has to denote. A satisfying assignment has to
realise the atoms it assigns, and a linear relaxation that treats `x * y` as a free column returns a
point where that column and the product of its coordinates disagree, so the point does not satisfy
the premises it was found for. `Refutation` therefore admits an atom only when it is a free variable
of type `real`, and a premise with a product in it is not one the solver may answer about.

**Amended 2026-09-11: the decision is per premise rather than per set.** The sentence that stood
here said that a premise set "not entirely about the reals" went back to the sampler, and that was
the rule, and it was the wrong shape for the sets people write. A claim about a domain is some
constraints over the reals and some over a declared type, so one premise the linear reader could not
take sent every other premise to the grid, and `{0 < cost, threatens a b}` was answered with a
hundred sampled points while half of it is a system and the other half is nine assignments.

The premises are partitioned now. The ones whose every atom is a free variable of type `real` are
one system; the rest are evaluated at each assignment of **their** free variables over the carriers
the model sized. The split is sound because the two halves share no variable, and that is a
consequence of the admission rule rather than an assumption about the caller: an atom of the system
is of type `real`, a variable of the other half is required to have a carrier, and `real` has none.
So the region does not move as the assignments do, and the simplex runs once rather than once per
assignment.

What the amendment does **not** do is make `Contradictory` a count. It is reported only where every
assignment was evaluated and none of them was feasible, or where the system alone has no point,
which is a decision whatever the other half says. One assignment this model could not evaluate
withdraws the claim to have decided anything, and the question goes back to the sampler with the
answer the sampler has. The enumeration is bounded, and a set larger than the bound goes back the
same way.

A decision over a declared type is a decision **about this model**, which is what every answer here
already is. `Contradictory` over the reals is near enough absolute because the intended model of the
reals is the reals; over a carrier sized at three it says that none of the nine assignments works,
and a model that sized the type differently is a different question. The distinction the seven
outcomes keep is a decision against a sample, not an absolute against a model-relative one, and
enumerating a carrier exhaustively is deciding.

The half that is still sampled is the half that is neither: a product of two unknowns, a variable of
type `num`, which is sampled rather than enumerated, a declared type the model never sized. Those
report what they have: points, and how many of them answered.

**Three things get worse or stay hard.**

`Double` is not the reals: addition on it is not associative, and the intended model would be a
counterexample to the very axioms it models were equality exact. It is not: equality of reals here
is the relative tolerance the `Expr` screening already uses. So the model satisfies the theory's
axioms because it is deliberately imprecise, and every answer it gives is an answer about that
imprecise arithmetic. `RefutationSpec` puts the sixteen axioms to it, and the fifteen it can evaluate hold.

A quantifier over the reals is not evaluated at all. `!x:real. p x` has no finite domain to
enumerate and no number of sample points makes it true, so the evaluator declines. The search opens
a universal **conclusion** into a free variable and samples it, which is sound because one point
refutes a universal; it does not do this to a **premise**, where one point would prove nothing and
the entailment would rest on a premise false elsewhere. The consequence is real and is not worked
around: a set of universally quantified premises over the reals cannot be checked for consistency
here, and the search says `NeverAsked` rather than reassuring anybody.

The eight logical constants are interpreted directly rather than unfolded, which is the one place
the system states something twice. `EvaluateSpec` closes it exhaustively rather than by sampling:
over `bool` a binary connective has four assignments and all four are compared against the
definition the kernel holds. For the propositional connectives that settles the agreement.

## Alternatives rejected

**Unfold the logical constants like everything else, and build in nothing.** The cleaner design,
and the one considered first: no second statement of what `/\` means and no possibility of drift.
It was rejected on cost, and the cost is counted rather than measured, because the variant was never
built. Conjunction is defined as an equation between two functions of type `bool -> bool -> bool`,
so evaluating one conjunction means enumerating that sixteen-element carrier and comparing two
functions across it, once per conjunction per candidate per sample point. The machinery is present
and reachable, which is how the agreement test evaluates the definitions at all; what was rejected
is routing every evaluation through it. The exhaustive agreement test recovers what the shortcut
gives up, and for the propositional connectives it recovers all of it rather than some.

**Evaluate through the algebra system by translating `Term` back to `Expr`.** Attractive because
`Expr.eval` exists and is tested. Rejected because the translation runs the wrong way across the
one border this repository guards: `Translate` is `Expr -> Term` and is thin on purpose, and an
inverse would have to interpret the logic, the quantifiers and the uninterpreted domain constants,
none of which `Expr` has. The evaluator would become a second, larger translator on the trusted
side's boundary, to save a hundred lines on the untrusted side.

**Sample a universal premise instead of declining it.** This is what makes the tool useful on the
corpora that motivated it, where the premises are general statements. Rejected because it produces
the one output this whole arrangement exists to prevent: a counterexample that is not one, standing
on a premise that held at the sampled point and fails elsewhere, reported with a witness that makes
it look checked. `NeverAsked` is a worse answer to receive and a true one.

**A carrier for `real` made of the sampled points, so that quantifiers become finite.** It would
make `!x:real. p x` evaluate, and it would be a lie with the shape of an answer: the model would
then satisfy `!x. p x` for any `p` true at the three hundred points chosen, and a reader has no way
to see that the domain was the sample. Declining is what keeps `Survived` and `true` distinguishable.

**Put the model on the trusted side and let a proof appeal to it.** A finite model can settle a
finite claim, and a system that enumerated a three-element domain could in principle emit a theorem.
Rejected by `0003`: this would put an evaluator, its arithmetic, and its tolerance inside the trusted
base, which is currently under 1200 lines and readable in an afternoon. The whole value of the
propose-and-check arrangement is that the proposing half can be wrong.
