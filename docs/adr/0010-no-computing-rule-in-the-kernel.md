# 0010. No computing rule in the kernel

- **Status:** accepted
- **Date:** 2026-09-11

## Context

Arithmetic here is derived, and that is expensive. `12 * 12 = 144` is 1132 primitive inferences,
because every carry is a rewrite justified by an axiom of the ring, and the numerals are binary
representations built from `BIT0` and `BIT1` rather than machine integers. The certificate-search
section of `docs/evaluation.md` measures the shape of the cost and the ladder section measures how
it grows.

Every mature system has met this and every one has answered it. Lean specialises `Nat` literals
onto GMP, so `12 * 12` is decided by a C library rather than by inference. Coq has `vm_compute` and
`native_compute`. HOL Light does not, and pays for it in exactly the way this system pays.

The cheapest version of the answer, for this system, would be a rule in the kernel that takes two
numerals and returns the theorem that their product is a third, computed with `BigInt`. It is a few
dozen lines. It would remove most of the constant factor on everything arithmetic, and it is the
only single change that would close the numeric gap with Lean.

## Decision

**There is no computing rule, and there will not be one while the trusted base is the argument.**

Numerals are computed with by derivation, through the axioms of the ring, and a proof of an
arithmetic fact records every step of it.

## Consequences

The constant factor stays. Where it can be recovered *outside* the kernel, it is: a tactic may use
any amount of machine arithmetic to **find** a certificate, because the certificate is then checked
by the ordinary rules. `Linarith`'s simplex is exact-rational machine arithmetic and produces a
Farkas combination that the kernel re-derives; `Ring` normalises with machine coefficients and
proves the normal forms equal. That division is the whole design and it is what `docs/adr/0003`
records one level up: the fast half proposes, the slow half checks.

What is given up is the class of goal where the *answer itself* is a large computation, and there
the honest statement is that this system is slower than Lean by a large factor and will stay so.

## The alternative, and why it was rejected

**A `Kernel.computeNumeral` rule.** Two numerals in, a theorem out, `BigInt` in the middle.

It was rejected on the one property this design has bought and has nothing else to buy it with: the
trusted base is four files under a bound, readable in an afternoon, and every rule in it is a
side-condition check on a term. A computing rule is a different kind of thing — it is an
implementation of arithmetic that has to be *correct*, and its correctness is not visible in the
way a side condition is. `BigInt` is the JDK's, the numeral encoding is ours, and the translation
between them is where the defect would live. It would be the only rule in the kernel whose failure
mode is a wrong theorem rather than a refused one.

Lean's version of this is a deliberate widening of its own trusted base and it is one of the
standard criticisms made of it. That is not an argument that Lean is wrong; it is an argument that
the two systems bought different things, and that buying both is not on offer.

**What would change this decision.** A consumer with a real goal that this system cannot reach for
this reason and no other, measured rather than supposed. `a119aa26` on Mycelium carries the smaller
version of the question — recovering the constant factor where measurement supports it, outside the
kernel — and this record exists so that the larger version is not re-decided by somebody who
reaches for the quick answer without knowing it was already refused once.

## What this does not cover

It says nothing about arithmetic in `modules/core`, which is the algebra system, is not trusted by
anything, and uses machine arithmetic throughout. It says nothing about `Evaluate` or `Refutation`,
which answer at a point with a `Double` and certify nothing, under `docs/adr/0005`.

And it is not a claim that derived arithmetic is fast enough. It is a claim about which of two
prices to pay.
