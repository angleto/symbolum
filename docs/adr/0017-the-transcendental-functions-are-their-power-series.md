# 0017. The transcendental functions are their power series

- **Status:** accepted
- **Date:** 2026-09-15

## Context

The front page of this repository carried one row saying, of the trigonometric, exponential and
logarithmic functions, **No. The theory has no constant for them**, and `docs/proving.md` has
listed them as the fourth thing to add since it was written, with the same one-line reason each
time: they need sequences. Neither document said what *defining* them would mean, so the row read
as a gap in the work rather than as a decision nobody had taken.

What made it a decision rather than an obvious step is that there are two honest ways to put a
constant into a theory here, and they differ in what they cost the reader rather than in how much
code they take. A constant can be **defined**, which costs nothing to believe and leaves every fact
about it to be proved; or it can be **asserted**, which is one line and puts a sentence into the
trusted base that `FoundationSpec` counts and that nothing in this repository can check.

Three things were already true and they bound the decision:

- `COMPLETENESS`, the sixteenth axiom of the reals, is what convergence is for, and until
  2026-09-13 nothing read it. `Peano.NUM_ARCHIMEDES` was the first thing to spend it.
- `Series` holds finite sums with linearity, monotonicity, the geometric sum and summation by
  parts, and `Coding` holds the factorial. Every ingredient of a power series existed except the
  limit.
- The repository's own rule is that a lemma is added by proving it, and `docs/adr/0007` commits to
  the axiom count coming **down** as the reals are constructed. Four new axioms about `exp`, `sin`,
  `cos` and `ln` would move it the other way, for a domain that is constructible from what is
  already here.

## Decision

**`exp`, `sin` and `cos` are defined as the limits of their power series, and `ln` as the inverse
of `exp` named by choice. No axiom is added.**

The limit is `Limit.lim`, itself a definition: `converges s l` is the epsilon-N statement and
`lim s` is `select (\l. converges s l)`. `Limit.CONVERGES_UNIQUE` is what turns *a* limit into
*the* limit, so `lim` is pinned wherever the sequence converges and silent where it does not.

**Convergence is not part of the definition.** `exp x` denotes at every real whether or not the
series at `x` converges, exactly as `NUM_GCD ZERO ZERO` denotes and as `NUM_FLOOR` denotes below
zero. What is provable about these constants is therefore exactly what somebody has proved
converges, which today is the value of each at zero and nothing else.

## Consequences

**A claim about them is a proposition now, which it was not.** `Ask` on
`sin x * sin x + cos x * cos x = 1` used to come back as a parse error about an unknown constant and
now comes back as a claim the prover cannot settle. Those are different answers and the second is
the one a reader can act on.

**The three values at zero are proved, and the route generalises to nothing.** At zero every series
here stops moving after its first term, so `Limit.CONVERGES_CONSTANT` with
`Limit.CONVERGES_EVENTUALLY` settles them with no convergence theorem at all. That is the whole of
what this trick buys: it says nothing about `exp 1`.

**What is not provable yet is a list, and it is longer than the definitions suggest.** That
`exp 1 > 2`, that `exp (x + y) = exp x * exp y`, that `sin` and `cos` satisfy the Pythagorean
identity, and every fact about `ln`. In the order the work wants them: the monotone convergence
theorem, which is where `COMPLETENESS` is spent a second time and which landed the same day as this
record, on 2026-09-15, as `Limit.MONOTONE_CONVERGES`; the comparison test, which
`SUM_MONOTONE` and `SUM_GEOMETRIC` are most of; the Cauchy product, for which `SUM_SWAP` is the
half that exists; and the intermediate value theorem, which wants continuity and is what every
fact about `ln` waits on.

**The cost is a reader who sees `exp` in the signature and assumes the analysis is behind it.**
That is paid in three places and nowhere else: the row in `README.md`, the docstring of
`Transcendental`, and this record.

**`0^0 = 1` is now load-bearing.** The first term of the exponential's series is `x^0 / 0!`, so
`POWER_ZERO` being unconditional is what makes `exp 0 = 1` come out. That convention was already in
`Series` and this is the first thing that depends on it.

## The hyperbolic pair, and why it is not a series

`sinh` and `cosh` landed in the same change and they are **not** power series: `sinh x` is
`(exp x - exp (-x)) / 2` and `cosh x` is the same with the other sign. That is a divergence from
the sentence above and it is deliberate, so it is recorded here rather than left for a reader to
find in the file.

The decision above is *defined rather than asserted*, and both routes satisfy it; what differs is
which definition. `sin` and `cos` are series **because there is nothing else here to define them
from**: the route through the exponential needs a complex one, and `docs/adr/0007` puts the
integers and the rationals before anything of that kind. The hyperbolic pair needs no such detour,
and taking it costs the development in two ways rather than one:

- **What is provable today.** From `exp`, `cosh x + sinh x = exp x` and `cosh x - sinh x =
  exp (-x)` are one linear step each, and the values at zero fall out of `EXP_ZERO`. From the
  series, the values at zero cost the argument `SIN_ZERO` costs and nothing else is provable at all.
- **What is provable later, which is the half that settles it.** Under the series definition the
  identity relating the pair to `exp` needs a rearrangement of a series into its even and odd
  parts, which is a theorem this repository does not have and would have to build. Under this one
  it is already there, and everything else about the pair follows from whatever gets proved about
  `exp`. A route whose first identity needs a missing theorem is not the cheaper one.

What it does **not** buy is the identity a reader expects next.
`cosh x * cosh x - sinh x * sinh x = 1` needs `exp x * exp (-x) = 1`, which is the addition
theorem, which wants the Cauchy product. The pair arrives with the same silence `exp` has.

## Alternatives rejected

**Assert a characterising axiom for each function.** One line each, and every fact about them would
follow the same day. It loses because the trusted base is the thing this repository asks to be
believed and these four are constructible from what is already in it, which is what `PRF-01` and
`docs/adr/0007` are about. There is a second reason that is worse and less obvious: a set of axioms
pinning `sin` and `cos` **uniquely** is not short, and a set that is subtly too weak is
unfalsifiable from inside the system. A wrong axiom about a constructed object is a theorem that
somebody eventually contradicts; a wrong axiom about an assumed one is a theory nobody can refute.

**Define each by `select` over a characterising predicate**, for instance `exp` as the function
satisfying `f 0 = 1` and `f (x + y) = f x * f y`. This costs no axiom either, so it is the
alternative that comes closest. It loses on two counts. Nothing is provable until the predicate is
shown inhabited, which needs the same analysis, so it buys no facts earlier; and the definition then
encodes a **claim about which properties characterise the function** rather than the function
itself, which is a claim a reader has to check and which would have to be revised if it turned out
to pin the wrong thing. The series is the function.

**Take the functions from the algebra half**, which already has `Sin`, `Cos` and `Exp` and evaluates
them numerically. Refused by `docs/adr/0003`: nothing the algebra side says is believed on the proof
side, and a constant whose meaning came from there would be the first exception.

**Wait for the analysis and define nothing until it is done.** This is the option with the cleanest
story and it is what the repository was doing by default. It loses because the constants are what
make the statements sayable, and a statement that cannot be written cannot be refused either: the
gap was invisible in the tooling and showed up as a parse error, which reads as the user's mistake
rather than as the system's limit. `docs/adr/0007`'s rule that an axiom arrives in the commit whose
derivation needs it is about **axioms**; these are definitions, and the same reasoning does not
carry over.

**Define `exp` first and get `sin` and `cos` from it through Euler's formula.** It is the shortest
route in a system that has the complex numbers. This one does not, and `docs/adr/0007` puts the
integers and the rationals before anything of that kind, so the two series cost less than the
detour.
