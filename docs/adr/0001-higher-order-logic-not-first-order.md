# 0001. Higher-order logic, not first-order

- **Status:** accepted
- **Date:** 2026-09-03

## Context

Symbolum is a rewriting system over an algebra of terms. It computes results and produces no
evidence for them, which is the difference between a computer algebra system and a proof
assistant: a prover produces an object a third party can re-check without trusting the process
that built it. Building that means choosing a logic before writing a line of the kernel, and the
choice is not reversible afterwards, because every derived rule, every theorem statement and
every tactic is written against it.

The pressure that decides it is already visible in the existing code. `Integral` and `Derivative`
bind a variable, and `replaceSymbol` does not know that: `Integral(x^2, "x").replaceSymbol("x",
3)` returns `Integral(9, "x")`, substituting into the body of a binder. Today that is a latent
defect in a CAS. In a kernel it would be a soundness hole. The operators the domain needs next,
sums, products, limits, suprema, are all binders too, so the question is not whether the system
handles binding but where binding lives: in the kernel, once, or in each operator.

## Decision

The kernel is a simply typed lambda calculus with equality as the primitive relation, in the
tradition of LCF and HOL: types built from type variables and type operators, terms built from
variables, constants, application and lambda abstraction, and a theorem as an abstract type
whose only constructors are the primitive inference rules.

Binders are not syntax. Each one is a constant whose argument is a function, so the integral over
a body is a constant applied to a lambda, and the single substitution in the kernel serves every
binder that will ever be defined.

## Consequences

A type system has to be written and maintained: type variables, type instantiation as a primitive
rule, and type inference in the parser so that surface syntax stays readable. That is real work
the first-order route would not have needed, on the order of a few days.

Adding a binder after that costs a constant definition and its characterising theorems, and
changes nothing in the trusted base. This is the property the decision was made for.

The trusted base carries none of the classical axioms this tradition usually adds: no
extensionality for functions, no choice operator, no axiom of infinity, and no rule for defining a
new type. The logic is correspondingly weaker than HOL proper: eta-equivalence is not provable,
there is no Hilbert choice, and no type of natural numbers can be carved out of `bool -> bool`.
Each can be added later, as an axiom or a kernel rule, in the same place and under the same
discipline as the sixteen axioms of the reals, and would enlarge what has to be believed by
exactly that much. Until one is, those sixteen axioms are the whole non-logical content of the
system. An earlier version of this record claimed the three axioms were present; an audit found
that none was, and that the claim had been inventing trusted content to audit.

What this does not cover: higher-order logic cannot express types that depend on values, so
formalisations that want a length-indexed vector have to encode it. Nothing in the intended
domain, real analysis and algebraic identities, needs that.

## Alternatives rejected

**Many-sorted first-order logic with equality.** Starts faster: no type system, no lambda, a
smaller kernel in the first week. It loses because every binder becomes a syntactic form with its
own substitution case and its own congruence rule inside the trusted base, so the trusted base
grows with the mathematics rather than staying fixed. Counting only the operators already known
to be needed, that is five kernel changes we can name today, each one a change to the code
nobody is allowed to get wrong.

**Dependent type theory (a calculus of constructions).** Strictly more expressive, gives proof
terms that an independent checker can verify without re-running the prover, and is what a system
started today at full scale would likely choose. It loses on scope: the kernel is an order of
magnitude larger, and its hardest component, the definitional equality checker with its
conversion and universe rules, is the part that would take the longest to get right and the part
where a subtle error is least visible. Rejected on cost, not on merit; if this system is ever
rebuilt, this is the alternative to reconsider first.

**Keeping the CAS and bolting a logic layer on top of `Expr`.** Rejected because `Expr` has no
notion of binding, no types, and a dozen rewrite rules that are false as unconditional identities
(cancellation without a non-zero hypothesis, `exp(log x) = x` without positivity, `(x^2)^(1/2) =
x`). Those are acceptable in an oracle and inadmissible in a kernel, and a layer on top cannot
undo them.
