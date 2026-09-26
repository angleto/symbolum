# What this system has proved

The results worth reading, each printed as its own page: the statement as the kernel holds it, what the proof
rests on, how it was derived where a derivation was recorded, and what it cost in axioms and in
inferences. The pages below the marker are generated; this section and the one after it are written
by hand, because they are arguments rather than renderings.

Nothing on a generated page is a copy. The statement is rendered from the term, the citations are
resolved by comparing sequents, the axioms come from walking the derivation, and the counts are
computed. So a page cannot be stale about its own theorem. What a page cannot tell you is whether
the theorem is worth anything, whether the constants are spelled the way the mathematics spells
them, or whether the statement says what the informal claim in your head says. The first is
mathematics, the second is recorded in `docs/reading-register.md`, and the third is what the legible
form printed under each statement is there for.

## How to regenerate it

    sbt "theories/runMain garden.xeno.symbolum.theories.Examples"

It replaces what lies between the two markers and leaves this prose alone. `ExamplesSpec` compares
the file against the code and fails naming that command, so the document breaks exactly when a
chosen theorem changes or disappears.

## What is not here, and what each absent thing would cost

This is the half of the document worth reading, and it is written by hand because a generator cannot
say what a system cannot do. The list is the areas that have been asked for, with the distance to
each measured against what the library actually holds rather than estimated.

| Area | Status | What stands in the way |
|---|---|---|
| Number theory over `num` | **partly here.** Bezout, Euclid's lemma, division with remainder, congruences, the gcd, the Chinese remainder theorem, the factorial, and since 2026-09-16 **unique factorisation**, both halves | The statement was what blocked it and the way round is worth knowing: uniqueness is usually a claim about a multiset of primes, and this system has no lists, no finite sets and no multisets. A factorisation here is a family and a length with the family asked to be **non-decreasing**, and then uniqueness is an equation between two families. What is still missing above it is anything that quantifies over "the divisors of `n`" as a collection, which wants the same absent machinery |
| The incompleteness theorems | **in progress.** The object language, both axiom sets, the proof predicate, closure under both rules of inference, and the first derivations of the embedded theory | `Prov` as a formula **of the object language** does not exist; what exists is `NUM_PROV`, a predicate of the ambient logic. D1, D2 and D3 are statements about that formula, so none of the three can be stated yet. `docs/adr/0013` is the plan |
| Analysis | **here for a first course, since 2026-09-25, and the pages are in the Analysis section below.** `Limit`, `Transcendental`, `Root`, `Continuity`, `Logarithm`, `Derivative` and `Integral` declare the limit, the six series functions, `sqrt`, continuity, the derivative and the gauge integral, and none of them costs an axiom. What is proved runs from `sqrt 2` being irrational and `exp (x + y) = exp x * exp y` through the intermediate value theorem, the extreme value theorem, Rolle and the mean value theorem to both halves of the fundamental theorem; `docs/proving.md` lists every fact under its development rather than this row copying them. **Nothing primitive was missing** for any of it: each was expressible over the theory as it stood, which is what this row claimed on 2026-09-14 when it said nothing was here | Measured against `docs/lemmas.md` on 2026-09-26, not estimated: continuity is closed under negation and under a linear map and **not** under a sum, a product or a composition, so a claim like "a polynomial is continuous" is one derivation per polynomial rather than a lemma; the derivative has the product and chain rules and no general rule for a sum; and there is no Taylor's theorem, no L'Hopital, and no series of functions |
| The fundamental theorem of algebra | **out of reach, and nothing about it is a decision** | It wants the complex numbers, so it wants the reals as a construction with the integers and the rationals under them, which `docs/adr/0007` puts in that order and which has not started. Then it wants an argument of its own: the route through Liouville wants a derivative, the route through winding numbers wants a topology, and neither exists here. Unlike the four colour theorem below it, what stands in the way is work rather than a recorded decision |
| The fundamental theorem of calculus | **here, both halves, since 2026-09-26** | `INTEGRAL_DERIVATIVE_WITHIN` is the first half in the form a textbook states it, the derivative one-sided at the ends, and over the gauge integral `docs/adr/0049` decides it needs no integrability hypothesis. `DERIVATIVE_INTEGRAL` is the second: the integral from `a` of a function continuous on `[a, b]` has that function as its derivative inside. Both have pages below. What it waited on was a derivative, then an integral, then additivity over intervals, and not the construction of the reals |
| The four colour theorem | **out of reach, and not only by size** | It needs graphs and finite sets, which do not exist, and the only proof anyone has runs a computation over 633 configurations. `docs/adr/0010` decides there is **no computing rule in the kernel** and that there will not be one while the trusted base is the argument, so the route Gonthier took is closed here by a recorded decision rather than by effort |
| Hilbert's solved problems | **out of reach, with one exception worth naming** | Most need machinery nothing here is near. The tenth, Matiyasevich's theorem, is the exception: it is a statement about Diophantine definability, and the beta function, the coding of sequences and the arithmetisation of syntax that the incompleteness work is building are the same ground floor. It is the one entry on this list that the current work walks towards rather than away from |

Two things this table is careful about. **"Nothing primitive is missing" and "it is a lot of work"
are different statements**, and analysis was the first kind of gap rather than the second, while the
four colour theorem is neither: it is blocked by a decision that was taken deliberately and written
down. The analysis row is what that distinction looks like once it is spent: written on 2026-09-14
as **nothing**, with the note that the definitions were expressible over the theory as it stands,
and rewritten on 2026-09-16 because `Limit` and `Transcendental` landed on 2026-09-15 and each asserts that
it moved the trusted base not at all. One day between the two, which is what "not blocked on
anything but work" was claiming and is the only kind of evidence that claim can have. What is
written in its place is the next rung rather than a second promise.

**There is a third kind of gap and the number theory row is it: the statement.** Unique
factorisation was not waiting on a primitive and was not waiting on volume of work. Every piece of
it existed for days, and what was missing was a way to say "the same factors" in a system with no
permutations and no multisets. The way round was to ask the family to be **non-decreasing**, which
turns the uniqueness into an equation between two families and costs the existence half one thing:
the factor taken off has to be the greatest prime divisor rather than any one of them. A gap of this
kind looks exactly like the second kind from outside, and the two are told apart by trying to write
the statement down rather than by estimating.

And **a rung that is reachable is not thereby cheap.** The entries marked partly here each took days
of work per theorem, and nothing below suggests the next one will be faster.

<!-- generated: examples, do not edit below this line -->

## Number theory

# NUM_PRIME_UNBOUNDED

$$\forall n \colon \mathbb{N}.\ \exists m \colon \mathbb{N}.\ \mathrm{prime}(m) \land n < m$$

```
!n:num. ?m:num. NUM_PRIME m /\ n < m
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 67 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_FACT_DIVIDES` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_FACTOR` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_LT_MONOTONE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

1244 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| EqualityElimination | 292 | 23.5% |
| Congruence | 280 | 22.5% |
| Reflexivity | 135 | 10.9% |
| Transitivity | 119 | 9.6% |
| BetaStep | 105 | 8.4% |
| Instantiation | 95 | 7.6% |
| Antisymmetry | 91 | 7.3% |
| TypeInstantiation | 46 | 3.7% |
| Assumption | 30 | 2.4% |
| Abstraction | 28 | 2.3% |
| Citation | 15 | 1.2% |
| Definition | 8 | 0.6% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. ?m:num. NUM_PRIME m /\ n < m"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PRIME_UNBOUNDED"
```

From Scala it is `Primes`'s, under the name `NUM_PRIME_UNBOUNDED`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_SQUARE_NOT_DOUBLE

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ 0 < m \Rightarrow \lnot \left( n \cdot n = \mathrm{suc}(\mathrm{suc}(0)) \cdot \left( m \cdot m \right) \right)$$

```
!n:num. !m:num. 0 < m ==> ~(n * n = SUC (SUC 0) * (m * m))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 75 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_EUCLID` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_DIVISOR` | Modular |
| `NUM_PRIME_TWO` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_CANCEL_LEFT` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_LT_MONOTONE` | Peano |
| `NUM_MUL_MONOTONE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

3162 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 847 | 26.8% |
| EqualityElimination | 683 | 21.6% |
| Reflexivity | 346 | 10.9% |
| Transitivity | 302 | 9.6% |
| Instantiation | 290 | 9.2% |
| BetaStep | 229 | 7.2% |
| Antisymmetry | 196 | 6.2% |
| TypeInstantiation | 116 | 3.7% |
| Assumption | 68 | 2.2% |
| Abstraction | 49 | 1.5% |
| Citation | 28 | 0.9% |
| Definition | 8 | 0.3% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. 0 < m ==> ~(n * n = SUC (SUC 0) * (m * m))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_SQUARE_NOT_DOUBLE"
```

From Scala it is `Primes`'s, under the name `NUM_SQUARE_NOT_DOUBLE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PRIME_TWO

$$\mathrm{prime}(\mathrm{suc}(\mathrm{suc}(0)))$$

```
NUM_PRIME (SUC (SUC 0))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 35 named facts in all.

| what | where |
|---|---|
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

1624 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| EqualityElimination | 392 | 24.1% |
| Congruence | 328 | 20.2% |
| Antisymmetry | 172 | 10.6% |
| Reflexivity | 157 | 9.7% |
| Instantiation | 156 | 9.6% |
| Transitivity | 122 | 7.5% |
| BetaStep | 100 | 6.2% |
| Assumption | 85 | 5.2% |
| TypeInstantiation | 51 | 3.1% |
| Abstraction | 39 | 2.4% |
| Citation | 11 | 0.7% |
| Definition | 11 | 0.7% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask NUM_PRIME (SUC (SUC 0))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PRIME_TWO"
```

From Scala it is `Modular`'s, under the name `NUM_PRIME_TWO`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PRIME_FACTOR

$$\forall n \colon \mathbb{N}.\ \mathrm{suc}(0) < n \Rightarrow \left( \exists m \colon \mathbb{N}.\ \mathrm{prime}(m) \land m \mid n \right)$$

```
!n:num. SUC 0 < n ==> (?m:num. NUM_PRIME m /\ NUM_DIVIDES m n)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 42 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

2649 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| EqualityElimination | 640 | 24.2% |
| Congruence | 576 | 21.7% |
| Antisymmetry | 281 | 10.6% |
| Instantiation | 261 | 9.9% |
| Reflexivity | 253 | 9.6% |
| Transitivity | 184 | 6.9% |
| BetaStep | 158 | 6.0% |
| Assumption | 127 | 4.8% |
| TypeInstantiation | 89 | 3.4% |
| Abstraction | 55 | 2.1% |
| Citation | 14 | 0.5% |
| Definition | 11 | 0.4% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. SUC 0 < n ==> (?m:num. NUM_PRIME m /\ NUM_DIVIDES m n)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PRIME_FACTOR"
```

From Scala it is `Modular`'s, under the name `NUM_PRIME_FACTOR`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_BEZOUT

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ \lnot \left( n = 0 \right) \lor \lnot \left( m = 0 \right) \Rightarrow \left( \exists k \colon \mathbb{N}.\ \exists i \colon \mathbb{N}.\ n \cdot k = m \cdot i + \gcd(n, m) \lor m \cdot k = n \cdot i + \gcd(n, m) \right)$$

```
!n:num. !m:num. ~(n = 0) \/ ~(m = 0) ==> (?k:num. ?i:num. n * k = m * i + NUM_GCD n m \/ m * k = n * i + NUM_GCD n m)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 60 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

8809 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2247 | 25.5% |
| EqualityElimination | 2053 | 23.3% |
| Instantiation | 858 | 9.7% |
| Reflexivity | 836 | 9.5% |
| Antisymmetry | 809 | 9.2% |
| Transitivity | 582 | 6.6% |
| BetaStep | 521 | 5.9% |
| TypeInstantiation | 344 | 3.9% |
| Assumption | 324 | 3.7% |
| Abstraction | 194 | 2.2% |
| Citation | 28 | 0.3% |
| Definition | 12 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. ~(n = 0) \/ ~(m = 0) ==> (?k:num. ?i:num. n * k = m * i + NUM_GCD n m \/ m * k = n * i + NUM_GCD n m)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_BEZOUT"
```

From Scala it is `Modular`'s, under the name `NUM_BEZOUT`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_EUCLID

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ \forall k \colon \mathbb{N}.\ \mathrm{prime}(n) \Rightarrow n \mid m \cdot k \Rightarrow n \mid m \lor n \mid k$$

```
!n:num. !m:num. !k:num. NUM_PRIME n ==> NUM_DIVIDES n (m * k) ==> NUM_DIVIDES n m \/ NUM_DIVIDES n k
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 63 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_DIVISOR` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

10238 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2576 | 25.2% |
| EqualityElimination | 2395 | 23.4% |
| Instantiation | 1014 | 9.9% |
| Reflexivity | 988 | 9.7% |
| Antisymmetry | 925 | 9.0% |
| Transitivity | 706 | 6.9% |
| BetaStep | 617 | 6.0% |
| TypeInstantiation | 403 | 3.9% |
| Assumption | 365 | 3.6% |
| Abstraction | 205 | 2.0% |
| Citation | 30 | 0.3% |
| Definition | 13 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. !k:num. NUM_PRIME n ==> NUM_DIVIDES n (m * k) ==> NUM_DIVIDES n m \/ NUM_DIVIDES n k"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_EUCLID"
```

From Scala it is `Modular`'s, under the name `NUM_EUCLID`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PRIME_DIVISOR

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ \mathrm{prime}(n) \Rightarrow m \mid n \Rightarrow m = \mathrm{suc}(0) \lor m = n$$

```
!n:num. !m:num. NUM_PRIME n ==> NUM_DIVIDES m n ==> m = SUC 0 \/ m = n
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

0 axioms reached, 0 of them named below, and 0 named facts in all.

It rests on no named fact, which means the inference rules alone.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

215 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 53 | 24.7% |
| Transitivity | 36 | 16.7% |
| EqualityElimination | 27 | 12.6% |
| Abstraction | 27 | 12.6% |
| Reflexivity | 21 | 9.8% |
| BetaStep | 20 | 9.3% |
| Antisymmetry | 9 | 4.2% |
| Assumption | 7 | 3.3% |
| Instantiation | 7 | 3.3% |
| Definition | 5 | 2.3% |
| TypeInstantiation | 3 | 1.4% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. NUM_PRIME n ==> NUM_DIVIDES m n ==> m = SUC 0 \/ m = n"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PRIME_DIVISOR"
```

From Scala it is `Modular`'s, under the name `NUM_PRIME_DIVISOR`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_FACTORISATION

$$\forall n \colon \mathbb{N}.\ \mathrm{suc}(0) < n \Rightarrow \left( \exists f \colon \mathbb{N} \to \mathbb{N}.\ \exists m \colon \mathbb{N}.\ 0 < m \land \left( \forall k \colon \mathbb{N}.\ k < m \Rightarrow \mathrm{prime}(f(k)) \right) \land \left( \forall k \colon \mathbb{N}.\ \forall i \colon \mathbb{N}.\ k < i \land i < m \Rightarrow f(k) \le f(i) \right) \land \prod_{i < m} f(i) = n \right)$$

```
!n:num. SUC 0 < n ==> (?f:num -> num. ?m:num. 0 < m /\ (!k:num. k < m ==> NUM_PRIME (f k)) /\ (!k:num. !i:num. k < i /\ i < m ==> f k <= f i) /\ NUM_PROD f m = n)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 68 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_PROD_CONG` | Coding |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_FACTOR` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_LT_MONOTONE` | Peano |
| `NUM_MUL_ONE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_STRONG_INDUCTION` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

4163 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 1323 | 31.8% |
| EqualityElimination | 871 | 20.9% |
| Reflexivity | 392 | 9.4% |
| Instantiation | 314 | 7.5% |
| Antisymmetry | 304 | 7.3% |
| Transitivity | 300 | 7.2% |
| BetaStep | 257 | 6.2% |
| TypeInstantiation | 140 | 3.4% |
| Abstraction | 115 | 2.8% |
| Assumption | 109 | 2.6% |
| Citation | 30 | 0.7% |
| Definition | 8 | 0.2% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. SUC 0 < n ==> (?f:num -> num. ?m:num. 0 < m /\ (!k:num. k < m ==> NUM_PRIME (f k)) /\ (!k:num. !i:num. k < i /\ i < m ==> f k <= f i) /\ NUM_PROD f m = n)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_FACTORISATION"
```

From Scala it is `Primes`'s, under the name `NUM_FACTORISATION`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_FACTORISATION_UNIQUE

$$\forall f \colon \mathbb{N} \to \mathbb{N}.\ \forall n \colon \mathbb{N}.\ \forall g \colon \mathbb{N} \to \mathbb{N}.\ \forall m \colon \mathbb{N}.\ \left( \forall k \colon \mathbb{N}.\ k < n \Rightarrow \mathrm{prime}(f(k)) \right) \Rightarrow \left( \forall k \colon \mathbb{N}.\ \forall i \colon \mathbb{N}.\ k < i \land i < n \Rightarrow f(k) \le f(i) \right) \Rightarrow \left( \forall k \colon \mathbb{N}.\ k < m \Rightarrow \mathrm{prime}(g(k)) \right) \Rightarrow \left( \forall k \colon \mathbb{N}.\ \forall i \colon \mathbb{N}.\ k < i \land i < m \Rightarrow g(k) \le g(i) \right) \Rightarrow \prod_{i < n} f(i) = \prod_{i < m} g(i) \Rightarrow n = m \land \left( \forall k \colon \mathbb{N}.\ k < n \Rightarrow f(k) = g(k) \right)$$

```
!f:num -> num. !n:num. !g:num -> num. !m:num. (!k:num. k < n ==> NUM_PRIME (f k)) ==> (!k:num. !i:num. k < i /\ i < n ==> f k <= f i) ==> (!k:num. k < m ==> NUM_PRIME (g k)) ==> (!k:num. !i:num. k < i /\ i < m ==> g k <= g i) ==> NUM_PROD f n = NUM_PROD g m ==> n = m /\ (!k:num. k < n ==> f k = g k)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 80 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_POSITIVE` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_EUCLID` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_DIVISOR` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_CANCEL_LEFT` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_LT_MONOTONE` | Peano |
| `NUM_MUL_ONE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_STRONG_INDUCTION` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `NUM_PRIME_DIVIDES_PROD` | Primes |
| `NUM_PRIME_PROD_ONE` | Primes |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

5972 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 1821 | 30.5% |
| EqualityElimination | 1311 | 22.0% |
| Reflexivity | 560 | 9.4% |
| Antisymmetry | 508 | 8.5% |
| Instantiation | 486 | 8.1% |
| Transitivity | 387 | 6.5% |
| BetaStep | 343 | 5.7% |
| TypeInstantiation | 193 | 3.2% |
| Assumption | 176 | 2.9% |
| Abstraction | 154 | 2.6% |
| Citation | 25 | 0.4% |
| Definition | 8 | 0.1% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:num -> num. !n:num. !g:num -> num. !m:num. (!k:num. k < n ==> NUM_PRIME (f k)) ==> (!k:num. !i:num. k < i /\ i < n ==> f k <= f i) ==> (!k:num. k < m ==> NUM_PRIME (g k)) ==> (!k:num. !i:num. k < i /\ i < m ==> g k <= g i) ==> NUM_PROD f n = NUM_PROD g m ==> n = m /\ (!k:num. k < n ==> f k = g k)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_FACTORISATION_UNIQUE"
```

From Scala it is `Primes`'s, under the name `NUM_FACTORISATION_UNIQUE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_CRT

$$\forall f \colon \mathbb{N} \to \mathbb{N}.\ \forall g \colon \mathbb{N} \to \mathbb{N}.\ \forall n \colon \mathbb{N}.\ \left( \forall m \colon \mathbb{N}.\ m < n \Rightarrow 0 < f(m) \right) \Rightarrow \left( \forall m \colon \mathbb{N}.\ \forall k \colon \mathbb{N}.\ m < n \land k < n \land \lnot \left( m = k \right) \Rightarrow \gcd(f(m), f(k)) = \mathrm{suc}(0) \right) \Rightarrow \left( \exists m \colon \mathbb{N}.\ \forall k \colon \mathbb{N}.\ k < n \Rightarrow m \equiv g(k) \pmod{f(k)} \right)$$

```
!f:num -> num. !g:num -> num. !n:num. (!m:num. m < n ==> 0 < f m) ==> (!m:num. !k:num. m < n /\ k < n /\ ~(m = k) ==> NUM_GCD (f m) (f k) = SUC 0) ==> (?m:num. !k:num. k < n ==> NUM_CONG (f k) m (g k))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 87 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_CRT_PAIR` | Coding |
| `NUM_GAUSS` | Coding |
| `NUM_GCD_MUL` | Coding |
| `NUM_GCD_PROD` | Coding |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_POSITIVE` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_CONG_DIVISOR` | Modular |
| `NUM_CONG_ELIM` | Modular |
| `NUM_CONG_INTRO` | Modular |
| `NUM_CONG_TRANS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_GCD_DIVIDES` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

11370 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 4180 | 36.8% |
| EqualityElimination | 2025 | 17.8% |
| Reflexivity | 973 | 8.6% |
| Instantiation | 890 | 7.8% |
| Transitivity | 853 | 7.5% |
| Antisymmetry | 726 | 6.4% |
| BetaStep | 630 | 5.5% |
| Abstraction | 463 | 4.1% |
| TypeInstantiation | 329 | 2.9% |
| Assumption | 255 | 2.2% |
| Citation | 35 | 0.3% |
| Definition | 10 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:num -> num. !g:num -> num. !n:num. (!m:num. m < n ==> 0 < f m) ==> (!m:num. !k:num. m < n /\ k < n /\ ~(m = k) ==> NUM_GCD (f m) (f k) = SUC 0) ==> (?m:num. !k:num. k < n ==> NUM_CONG (f k) m (g k))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_CRT"
```

From Scala it is `Coding`'s, under the name `NUM_CRT`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_FACT_DIVIDES

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ 0 < n \land n \le m \Rightarrow n \mid m!$$

```
!n:num. !m:num. 0 < n /\ n <= m ==> NUM_DIVIDES n (NUM_FACT m)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 40 named facts in all.

| what | where |
|---|---|
| `NUM_FACT_SUC` | Coding |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

4501 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2062 | 45.8% |
| EqualityElimination | 612 | 13.6% |
| Abstraction | 329 | 7.3% |
| Transitivity | 308 | 6.8% |
| Reflexivity | 278 | 6.2% |
| Antisymmetry | 249 | 5.5% |
| Instantiation | 230 | 5.1% |
| BetaStep | 221 | 4.9% |
| Assumption | 102 | 2.3% |
| TypeInstantiation | 88 | 2.0% |
| Citation | 12 | 0.3% |
| Definition | 9 | 0.2% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. 0 < n /\ n <= m ==> NUM_DIVIDES n (NUM_FACT m)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_FACT_DIVIDES"
```

From Scala it is `Coding`'s, under the name `NUM_FACT_DIVIDES`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

## The naturals, and what separates the reals from an ordered field

# NUM_STRONG_INDUCTION

$$\forall f \colon \mathbb{N} \to \mathbb{B}.\ \left( \forall n \colon \mathbb{N}.\ \left( \forall m \colon \mathbb{N}.\ m < n \Rightarrow f(m) \right) \Rightarrow f(n) \right) \Rightarrow \left( \forall n \colon \mathbb{N}.\ f(n) \right)$$

```
!f:num -> bool. (!n:num. (!m:num. m < n ==> f m) ==> f n) ==> (!n:num. f n)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 17 named facts in all.

| what | where |
|---|---|
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

5356 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2236 | 41.7% |
| EqualityElimination | 832 | 15.5% |
| Reflexivity | 358 | 6.7% |
| Transitivity | 350 | 6.5% |
| Abstraction | 350 | 6.5% |
| Antisymmetry | 350 | 6.5% |
| Instantiation | 323 | 6.0% |
| BetaStep | 267 | 5.0% |
| Assumption | 148 | 2.8% |
| TypeInstantiation | 126 | 2.4% |
| Definition | 11 | 0.2% |
| Citation | 4 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:num -> bool. (!n:num. (!m:num. m < n ==> f m) ==> f n) ==> (!n:num. f n)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_STRONG_INDUCTION"
```

From Scala it is `Peano`'s, under the name `NUM_STRONG_INDUCTION`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_ARCHIMEDES

$$\forall x \colon \mathbb{R}.\ \exists n \colon \mathbb{N}.\ x < n_{\mathbb{R}}$$

```
!x:real. ?n:num. x < real_of_num n
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 15 of them named below, and 43 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `NUM_REAL_SUC` | Peano |
| `ADD_POSITIVE` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `real_le` | Real, defined |
| `sub` | Real, defined |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

11323 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 3962 | 35.0% |
| EqualityElimination | 1972 | 17.4% |
| Transitivity | 1161 | 10.3% |
| Reflexivity | 1103 | 9.7% |
| Instantiation | 973 | 8.6% |
| BetaStep | 711 | 6.3% |
| Antisymmetry | 454 | 4.0% |
| Abstraction | 412 | 3.6% |
| TypeInstantiation | 390 | 3.4% |
| Assumption | 151 | 1.3% |
| Citation | 12 | 0.1% |
| Axiom | 12 | 0.1% |
| Definition | 10 | 0.1% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. ?n:num. x < real_of_num n"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_ARCHIMEDES"
```

From Scala it is `Peano`'s, under the name `NUM_ARCHIMEDES`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# ABS_TRIANGLE

$$\forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert$$

```
!x:real. !y:real. abs (x + y) <= abs x + abs y
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

11 axioms reached, 10 of them named below, and 30 named facts in all.

| what | where |
|---|---|
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `ADD_LE` | Order |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `ADD_POSITIVE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

70 steps, recorded as the derivation was written.

1. by the order is total
   $\vdash \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x < y \lor x = y \lor y < x$
2. specialise at x, y from LT_TOTAL
   $\vdash x < y \lor x = y \lor y < x$
3. on the right of y = x
   $\vdash y = x \lor y = y$
4. on the left of x = y
   $\vdash x = x \lor x = y$
5. specialise at x, x from LE_OF_EQ
   $\vdash x = x \Rightarrow x \le x$
6. modus ponens from step 5
   $\vdash x \le x$
7. specialise at y, y from LE_OF_EQ
   $\vdash y = y \Rightarrow y \le y$
8. modus ponens from step 7
   $\vdash y \le y$
9. assume x < y
   $x < y \vdash x < y$
10. specialise at x, y from LE_OF_LT
   $\vdash x < y \Rightarrow x \le y$
11. modus ponens from step 10 and step 9
   $x < y \vdash x \le y$
12. and from step 11 and step 8
   $x < y \vdash x \le y \land y \le y$
13. and from step 3 and step 12
   $x < y \vdash \left( y = x \lor y = y \right) \land x \le y \land y \le y$
14. so there is one namely y from step 13
   $x < y \vdash \exists z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z$
15. assume x = y
   $x = y \vdash x = y$
16. specialise at x, y from LE_OF_EQ
   $\vdash x = y \Rightarrow x \le y$
17. modus ponens from step 16 and step 15
   $x = y \vdash x \le y$
18. and from step 17 and step 8
   $x = y \vdash x \le y \land y \le y$
19. and from step 3 and step 18
   $x = y \vdash \left( y = x \lor y = y \right) \land x \le y \land y \le y$
20. so there is one namely y from step 19
   $x = y \vdash \exists z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z$
21. assume y < x
   $y < x \vdash y < x$
22. specialise at y, x from LE_OF_LT
   $\vdash y < x \Rightarrow y \le x$
23. modus ponens from step 22 and step 21
   $y < x \vdash y \le x$
24. and from step 6 and step 23
   $y < x \vdash x \le x \land y \le x$
25. and from step 4 and step 24
   $y < x \vdash \left( x = x \lor x = y \right) \land x \le x \land y \le x$
26. so there is one namely x from step 25
   $y < x \vdash \exists z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z$
27. assume x = y \/ y < x
   $x = y \lor y < x \vdash x = y \lor y < x$
28. either way from step 27 and step 20 and step 26
   $x = y \lor y < x \vdash \exists z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z$
29. either way from step 2 and step 14 and step 28
   $\vdash \exists z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z$
30. name it by choice max from step 29
   $\vdash \left( \lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z \right)(\varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z))$
31. beta reduce
   $\vdash \left( \lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z \right)(\varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z)) = \left( \left( \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) = x \lor \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) = y \right) \land x \le \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) \land y \le \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) \right)$
32. replace from step 31 and step 30
   $\vdash \left( \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) = x \lor \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) = y \right) \land x \le \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z) \land y \le \varepsilon(\lambda z \colon \mathbb{R}.\ \left( z = x \lor z = y \right) \land x \le z \land y \le z)$
33. rewrite with the definition of max from step 32 and the definition of max
   $\vdash \left( \max(x, y) = x \lor \max(x, y) = y \right) \land x \le \max(x, y) \land y \le \max(x, y)$
34. the first half from step 33
   $\vdash \max(x, y) = x \lor \max(x, y) = y$
35. generalise over x, y from step 34
   $\vdash \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \max(x, y) = x \lor \max(x, y) = y$
36. specialise at x, -x from MAX_CASES
   $\vdash \max(x, - x) = x \lor \max(x, - x) = - x$
37. rewrite with the definition of abs from step 36 and the definition of abs
   $\vdash \lvert x \rvert = x \lor \lvert x \rvert = - x$
38. generalise over x from step 37
   $\vdash \forall x \colon \mathbb{R}.\ \lvert x \rvert = x \lor \lvert x \rvert = - x$
39. the second half from step 33
   $\vdash x \le \max(x, y) \land y \le \max(x, y)$
40. the first half from step 39
   $\vdash x \le \max(x, y)$
41. generalise over x, y from step 40
   $\vdash \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x \le \max(x, y)$
42. specialise at x, -x from MAX_ABOVE_LEFT
   $\vdash x \le \max(x, - x)$
43. rewrite with the definition of abs from step 42 and the definition of abs
   $\vdash x \le \lvert x \rvert$
44. generalise over x from step 43
   $\vdash \forall x \colon \mathbb{R}.\ x \le \lvert x \rvert$
45. the second half from step 39
   $\vdash y \le \max(x, y)$
46. generalise over x, y from step 45
   $\vdash \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ y \le \max(x, y)$
47. specialise at x, -x from MAX_ABOVE_RIGHT
   $\vdash - x \le \max(x, - x)$
48. rewrite with the definition of abs from step 47 and the definition of abs
   $\vdash - x \le \lvert x \rvert$
49. generalise over x from step 48
   $\vdash \forall x \colon \mathbb{R}.\ - x \le \lvert x \rvert$
50. specialise at x from ABS_ABOVE
   $\vdash x \le \lvert x \rvert$
51. specialise at y from ABS_ABOVE
   $\vdash y \le \lvert y \rvert$
52. specialise at x from ABS_ABOVE_NEG
   $\vdash - x \le \lvert x \rvert$
53. specialise at y from ABS_ABOVE_NEG
   $\vdash - y \le \lvert y \rvert$
54. specialise at x, abs x, y, abs y from ADD_LE
   $\vdash x \le \lvert x \rvert \Rightarrow y \le \lvert y \rvert \Rightarrow x + y \le \lvert x \rvert + \lvert y \rvert$
55. modus ponens from step 54 and step 43
   $\vdash y \le \lvert y \rvert \Rightarrow x + y \le \lvert x \rvert + \lvert y \rvert$
56. modus ponens from step 55 and step 51
   $\vdash x + y \le \lvert x \rvert + \lvert y \rvert$
57. specialise at -x, abs x, -y, abs y from ADD_LE
   $\vdash - x \le \lvert x \rvert \Rightarrow - y \le \lvert y \rvert \Rightarrow - x + - y \le \lvert x \rvert + \lvert y \rvert$
58. modus ponens from step 57 and step 48
   $\vdash - y \le \lvert y \rvert \Rightarrow - x + - y \le \lvert x \rvert + \lvert y \rvert$
59. modus ponens from step 58 and step 53
   $\vdash - x + - y \le \lvert x \rvert + \lvert y \rvert$
60. RING -x + -y = -(x + y)
   $\vdash - x + - y = - \left( x + y \right)$
61. rewrite both sides from step 59 and step 60
   $\vdash - \left( x + y \right) \le \lvert x \rvert + \lvert y \rvert$
62. specialise at x + y from ABS_CASES
   $\vdash \lvert x + y \rvert = x + y \lor \lvert x + y \rvert = - \left( x + y \right)$
63. assume abs (x + y) = x + y
   $\lvert x + y \rvert = x + y \vdash \lvert x + y \rvert = x + y$
64. read backwards from step 63
   $\lvert x + y \rvert = x + y \vdash x + y = \lvert x + y \rvert$
65. rewrite both sides from step 56 and step 64
   $\lvert x + y \rvert = x + y \vdash \lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert$
66. assume abs (x + y) = -(x + y)
   $\lvert x + y \rvert = - \left( x + y \right) \vdash \lvert x + y \rvert = - \left( x + y \right)$
67. read backwards from step 66
   $\lvert x + y \rvert = - \left( x + y \right) \vdash - \left( x + y \right) = \lvert x + y \rvert$
68. rewrite both sides from step 61 and step 67
   $\lvert x + y \rvert = - \left( x + y \right) \vdash \lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert$
69. either way from step 62 and step 65 and step 68
   $\vdash \lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert$
70. generalise over x, y from step 69
   $\vdash \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert$

## The proof the kernel holds

3873 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 1023 | 26.4% |
| EqualityElimination | 844 | 21.8% |
| Reflexivity | 453 | 11.7% |
| Transitivity | 401 | 10.4% |
| Instantiation | 317 | 8.2% |
| BetaStep | 309 | 8.0% |
| TypeInstantiation | 177 | 4.6% |
| Antisymmetry | 177 | 4.6% |
| Abstraction | 91 | 2.3% |
| Assumption | 61 | 1.6% |
| Axiom | 9 | 0.2% |
| Definition | 8 | 0.2% |
| Citation | 3 | 0.1% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. !y:real. abs (x + y) <= abs x + abs y"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find ABS_TRIANGLE"
```

From Scala it is `Magnitude`'s, under the name `ABS_TRIANGLE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.
- Each step is one operation as it was recorded, and a step citing a name cites a fact whose
  statement is that name's.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

## Analysis

# SQRT_TWO_IRRATIONAL

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ 0 < m \Rightarrow \lnot \left( \sqrt{2} = n_{\mathbb{R}} / m_{\mathbb{R}} \right)$$

```
!n:num. !m:num. 0 < m ==> ~(sqrt 2 = real_of_num n / real_of_num m)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

18 axioms reached, 16 of them named below, and 124 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_EUCLID` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_PRIME_ABOVE_ONE` | Modular |
| `NUM_PRIME_DIVISOR` | Modular |
| `NUM_PRIME_TWO` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_CANCEL_LEFT` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_LT_MONOTONE` | Peano |
| `NUM_MUL_MONOTONE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_REAL_ADD` | Peano |
| `NUM_REAL_INJECTIVE` | Peano |
| `NUM_REAL_LE` | Peano |
| `NUM_REAL_LT` | Peano |
| `NUM_REAL_MUL` | Peano |
| `NUM_REAL_NONNEG` | Peano |
| `NUM_REAL_SUC` | Peano |
| `NUM_REAL_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `NUM_SQUARE_NOT_DOUBLE` | Primes |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |
| `SQRT` | Root |
| `SQRT_EXISTS` | Root |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

48229 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 14100 | 29.2% |
| EqualityElimination | 7776 | 16.1% |
| Transitivity | 7414 | 15.4% |
| Instantiation | 7407 | 15.4% |
| Reflexivity | 5329 | 11.0% |
| BetaStep | 2623 | 5.4% |
| Antisymmetry | 1812 | 3.8% |
| TypeInstantiation | 1175 | 2.4% |
| Assumption | 354 | 0.7% |
| Abstraction | 193 | 0.4% |
| Citation | 20 | 0.0% |
| Axiom | 14 | 0.0% |
| Definition | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. 0 < m ==> ~(sqrt 2 = real_of_num n / real_of_num m)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find SQRT_TWO_IRRATIONAL"
```

From Scala it is `Root`'s, under the name `SQRT_TWO_IRRATIONAL`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# EXP_ADD

$$\forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \exp \left( x + y \right) = \exp x \cdot \exp y$$

```
!x:real. !y:real. exp (x + y) = exp x * exp y
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

19 axioms reached, 16 of them named below, and 190 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `NOT_FORALL` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_CHOOSE_FACTORIAL` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `CONVERGES_ABSOLUTE` | Limit |
| `CONVERGES_ADD` | Limit |
| `CONVERGES_EVENTUALLY` | Limit |
| `CONVERGES_GE` | Limit |
| `CONVERGES_LE` | Limit |
| `CONVERGES_MUL` | Limit |
| `CONVERGES_NEG` | Limit |
| `CONVERGES_TO_ZERO` | Limit |
| `CONVERGES_UNIQUE` | Limit |
| `LE_BELOW_EVERY_POSITIVE` | Limit |
| `LIM_OF_CONVERGES` | Limit |
| `MONOTONE_CONVERGES` | Limit |
| `MONOTONE_LE` | Limit |
| `SUM_ABS` | Limit |
| `SUM_BELOW_LIMIT` | Limit |
| `SUM_CAUCHY_BELOW_SQUARE` | Limit |
| `SUM_CAUCHY_PRODUCT` | Limit |
| `SUM_CAUCHY_PRODUCT_NONNEG` | Limit |
| `SUM_COMPARISON` | Limit |
| `SUM_GROWS` | Limit |
| `SUM_SQUARE_BELOW_CAUCHY` | Limit |
| `SUM_TAIL_ABS` | Limit |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_MUL` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `ABS_TRIANGLE` | Magnitude |
| `ABS_ZERO` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `ADD_LE` | Order |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `INV_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_MUL_BOTH` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_OF_NOT_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_MUL_BOTH` | Order |
| `LT_OF_NOT_LE` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_ARCHIMEDES` | Peano |
| `NUM_CEIL_LE` | Peano |
| `NUM_CHOOSE_ABOVE` | Peano |
| `NUM_CHOOSE_ALL` | Peano |
| `NUM_CHOOSE_EMPTY` | Peano |
| `NUM_CHOOSE_SUC` | Peano |
| `NUM_CHOOSE_ZERO` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_DOUBLE_SUB` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_OF_LT_SUC` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_PRE_LE` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_PRE_ZERO` | Peano |
| `NUM_REAL_ADD` | Peano |
| `NUM_REAL_LE` | Peano |
| `NUM_REAL_LT` | Peano |
| `NUM_REAL_MUL` | Peano |
| `NUM_REAL_NONNEG` | Peano |
| `NUM_REAL_SUC` | Peano |
| `NUM_REAL_ZERO` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_LE` | Peano |
| `NUM_SUB_REFL` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_SUC_SUB` | Peano |
| `NUM_SUC_SUB_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |
| `POWER_BINOMIAL` | Series |
| `POWER_POSITIVE` | Series |
| `POWER_SUC` | Series |
| `POWER_ZERO` | Series |
| `SUM_ADD` | Series |
| `SUM_CAUCHY` | Series |
| `SUM_CAUCHY_GAP` | Series |
| `SUM_CONGRUENCE` | Series |
| `SUM_CONGRUENCE_BELOW` | Series |
| `SUM_DIAGONAL` | Series |
| `SUM_GEOMETRIC` | Series |
| `SUM_HALVES` | Series |
| `SUM_MONOTONE` | Series |
| `SUM_MONOTONE_BELOW` | Series |
| `SUM_NONNEGATIVE` | Series |
| `SUM_REINDEX` | Series |
| `SUM_SCALE` | Series |
| `SUM_SCALE_RIGHT` | Series |
| `SUM_SHIFT` | Series |
| `SUM_SUC` | Series |
| `SUM_ZERO` | Series |
| `EXP_ABSOLUTE` | Transcendental |
| `EXP_CONVOLUTION` | Transcendental |
| `EXP_TAIL_GEOMETRIC` | Transcendental |
| `EXP_TERM_HALVES` | Transcendental |
| `MUL_INV_COMBINE` | Transcendental |

3 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

34824 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 10775 | 30.9% |
| EqualityElimination | 6074 | 17.4% |
| Transitivity | 4632 | 13.3% |
| Instantiation | 4451 | 12.8% |
| Reflexivity | 3914 | 11.2% |
| BetaStep | 2025 | 5.8% |
| Antisymmetry | 1309 | 3.8% |
| TypeInstantiation | 1019 | 2.9% |
| Abstraction | 318 | 0.9% |
| Assumption | 221 | 0.6% |
| Citation | 60 | 0.2% |
| Axiom | 13 | 0.0% |
| Definition | 13 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. !y:real. exp (x + y) = exp x * exp y"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find EXP_ADD"
```

From Scala it is `Transcendental`'s, under the name `EXP_ADD`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# SIN_COS_SQUARED

$$\forall x \colon \mathbb{R}.\ \sin x \cdot \sin x + \cos x \cdot \cos x = 1$$

```
!x:real. sin x * sin x + cos x * cos x = 1
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

19 axioms reached, 16 of them named below, and 203 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `NOT_FORALL` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_CHOOSE_FACTORIAL` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `ABS_POWER_LE` | Limit |
| `CONVERGES_ABSOLUTE` | Limit |
| `CONVERGES_ADD` | Limit |
| `CONVERGES_CONSTANT` | Limit |
| `CONVERGES_EVENTUALLY` | Limit |
| `CONVERGES_GE` | Limit |
| `CONVERGES_LE` | Limit |
| `CONVERGES_MUL` | Limit |
| `CONVERGES_NEG` | Limit |
| `CONVERGES_SHIFT` | Limit |
| `CONVERGES_TO_ZERO` | Limit |
| `CONVERGES_UNIQUE` | Limit |
| `LE_BELOW_EVERY_POSITIVE` | Limit |
| `LIM_OF_CONVERGES` | Limit |
| `MONOTONE_CONVERGES` | Limit |
| `MONOTONE_LE` | Limit |
| `SUM_ABS` | Limit |
| `SUM_BELOW_LIMIT` | Limit |
| `SUM_CAUCHY_BELOW_SQUARE` | Limit |
| `SUM_CAUCHY_PRODUCT` | Limit |
| `SUM_CAUCHY_PRODUCT_NONNEG` | Limit |
| `SUM_COMPARISON` | Limit |
| `SUM_GROWS` | Limit |
| `SUM_SQUARE_BELOW_CAUCHY` | Limit |
| `SUM_TAIL_ABS` | Limit |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_MUL` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `ABS_TRIANGLE` | Magnitude |
| `ABS_ZERO` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `ADD_LE` | Order |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `INV_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_MUL_BOTH` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_OF_NOT_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_MUL_BOTH` | Order |
| `LT_OF_NOT_LE` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_ARCHIMEDES` | Peano |
| `NUM_BIT0_ADD` | Peano |
| `NUM_CEIL_LE` | Peano |
| `NUM_CHOOSE_ABOVE` | Peano |
| `NUM_CHOOSE_ALL` | Peano |
| `NUM_CHOOSE_EMPTY` | Peano |
| `NUM_CHOOSE_SUC` | Peano |
| `NUM_CHOOSE_ZERO` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_DOUBLE_SUB` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_OF_LT_SUC` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_ONE_SUC` | Peano |
| `NUM_PRE_LE` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_PRE_ZERO` | Peano |
| `NUM_REAL_ADD` | Peano |
| `NUM_REAL_LE` | Peano |
| `NUM_REAL_LT` | Peano |
| `NUM_REAL_MUL` | Peano |
| `NUM_REAL_NONNEG` | Peano |
| `NUM_REAL_SUC` | Peano |
| `NUM_REAL_ZERO` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_LE` | Peano |
| `NUM_SUB_REFL` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_SUC_SUB` | Peano |
| `NUM_SUC_SUB_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `NUM_ZERO_SUB` | Peano |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |
| `POWER_ADD` | Series |
| `POWER_BINOMIAL` | Series |
| `POWER_NEG_DOUBLE` | Series |
| `POWER_ONE` | Series |
| `POWER_POSITIVE` | Series |
| `POWER_SUC` | Series |
| `POWER_ZERO` | Series |
| `SUM_ADD` | Series |
| `SUM_CAUCHY` | Series |
| `SUM_CAUCHY_GAP` | Series |
| `SUM_CONGRUENCE` | Series |
| `SUM_CONGRUENCE_BELOW` | Series |
| `SUM_DIAGONAL` | Series |
| `SUM_EVEN_ODD` | Series |
| `SUM_GEOMETRIC` | Series |
| `SUM_HALVES` | Series |
| `SUM_MONOTONE` | Series |
| `SUM_MONOTONE_BELOW` | Series |
| `SUM_NONNEGATIVE` | Series |
| `SUM_OF_ZERO` | Series |
| `SUM_REINDEX` | Series |
| `SUM_SCALE` | Series |
| `SUM_SCALE_RIGHT` | Series |
| `SUM_SHIFT` | Series |
| `SUM_SUC` | Series |
| `SUM_ZERO` | Series |
| `COS_ABSOLUTE` | Transcendental |
| `EXP_ABSOLUTE` | Transcendental |
| `EXP_CONVOLUTION` | Transcendental |
| `EXP_TAIL_GEOMETRIC` | Transcendental |
| `EXP_TERM_HALVES` | Transcendental |
| `MUL_INV_COMBINE` | Transcendental |
| `SIN_ABSOLUTE` | Transcendental |

3 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

62016 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 22017 | 35.5% |
| EqualityElimination | 9176 | 14.8% |
| Transitivity | 8589 | 13.8% |
| Instantiation | 8296 | 13.4% |
| Reflexivity | 6637 | 10.7% |
| BetaStep | 3032 | 4.9% |
| Antisymmetry | 1844 | 3.0% |
| TypeInstantiation | 1450 | 2.3% |
| Abstraction | 535 | 0.9% |
| Assumption | 322 | 0.5% |
| Citation | 91 | 0.1% |
| Definition | 14 | 0.0% |
| Axiom | 13 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. sin x * sin x + cos x * cos x = 1"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find SIN_COS_SQUARED"
```

From Scala it is `Transcendental`'s, under the name `SIN_COS_SQUARED`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# INTERMEDIATE_VALUE

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \forall z \colon \mathbb{R}.\ x \le y \Rightarrow \left( \forall u \colon \mathbb{R}.\ x \le u \land u \le y \Rightarrow \operatorname{cont}(f, u) \right) \Rightarrow f(x) \le z \Rightarrow z \le f(y) \Rightarrow \left( \exists u \colon \mathbb{R}.\ x \le u \land u \le y \land f(u) = z \right)$$

```
!f:real -> real. !x:real. !y:real. !z:real. x <= y ==> (!u:real. x <= u /\ u <= y ==> continuous f u) ==> f x <= z ==> z <= f y ==> (?u:real. x <= u /\ u <= y /\ f u = z)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 51 named facts in all.

| what | where |
|---|---|
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

28128 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 7856 | 27.9% |
| EqualityElimination | 5396 | 19.2% |
| Transitivity | 3699 | 13.2% |
| Instantiation | 3416 | 12.1% |
| Reflexivity | 3223 | 11.5% |
| BetaStep | 1828 | 6.5% |
| Antisymmetry | 1333 | 4.7% |
| TypeInstantiation | 901 | 3.2% |
| Assumption | 233 | 0.8% |
| Abstraction | 192 | 0.7% |
| Citation | 26 | 0.1% |
| Axiom | 13 | 0.0% |
| Definition | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !x:real. !y:real. !z:real. x <= y ==> (!u:real. x <= u /\ u <= y ==> continuous f u) ==> f x <= z ==> z <= f y ==> (?u:real. x <= u /\ u <= y /\ f u = z)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find INTERMEDIATE_VALUE"
```

From Scala it is `Continuity`'s, under the name `INTERMEDIATE_VALUE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# CONTINUOUS_ATTAINS_MAX

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x \le y \Rightarrow \left( \forall z \colon \mathbb{R}.\ x \le z \land z \le y \Rightarrow \operatorname{cont}(f, z) \right) \Rightarrow \left( \exists z \colon \mathbb{R}.\ x \le z \land z \le y \land \left( \forall u \colon \mathbb{R}.\ x \le u \land u \le y \Rightarrow f(u) \le f(z) \right) \right)$$

```
!f:real -> real. !x:real. !y:real. x <= y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (?z:real. x <= z /\ z <= y /\ (!u:real. x <= u /\ u <= y ==> f u <= f z))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 49 named facts in all.

| what | where |
|---|---|
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `CONTINUOUS_BOUNDED` | Continuity |
| `INTERVAL_GLUING` | Continuity |
| `ABS_ABOVE` | Magnitude |
| `ABS_CASES` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

49522 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 14070 | 28.4% |
| EqualityElimination | 9298 | 18.8% |
| Transitivity | 6382 | 12.9% |
| Instantiation | 6241 | 12.6% |
| Reflexivity | 5492 | 11.1% |
| BetaStep | 2960 | 6.0% |
| Antisymmetry | 2587 | 5.2% |
| TypeInstantiation | 1487 | 3.0% |
| Assumption | 516 | 1.0% |
| Abstraction | 436 | 0.9% |
| Citation | 28 | 0.1% |
| Axiom | 13 | 0.0% |
| Definition | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !x:real. !y:real. x <= y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (?z:real. x <= z /\ z <= y /\ (!u:real. x <= u /\ u <= y ==> f u <= f z))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find CONTINUOUS_ATTAINS_MAX"
```

From Scala it is `Continuity`'s, under the name `CONTINUOUS_ATTAINS_MAX`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# ROLLE

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x < y \Rightarrow \left( \forall z \colon \mathbb{R}.\ x \le z \land z \le y \Rightarrow \operatorname{cont}(f, z) \right) \Rightarrow \left( \forall z \colon \mathbb{R}.\ x < z \land z < y \Rightarrow \left( \exists u \colon \mathbb{R}.\ \operatorname{deriv}(f, z, u) \right) \right) \Rightarrow f(x) = f(y) \Rightarrow \left( \exists z \colon \mathbb{R}.\ x < z \land z < y \land \operatorname{deriv}(f, z, 0) \right)$$

```
!f:real -> real. !x:real. !y:real. x < y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (!z:real. x < z /\ z < y ==> (?u:real. derivative f z u)) ==> f x = f y ==> (?z:real. x < z /\ z < y /\ derivative f z 0)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 61 named facts in all.

| what | where |
|---|---|
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `CONTINUOUS_ATTAINS_MAX` | Continuity |
| `CONTINUOUS_ATTAINS_MIN` | Continuity |
| `CONTINUOUS_BOUNDED` | Continuity |
| `CONTINUOUS_NEG` | Continuity |
| `INTERVAL_GLUING` | Continuity |
| `DERIVATIVE_INTERIOR_MAX` | Derivative |
| `DERIVATIVE_INTERIOR_MIN` | Derivative |
| `DERIVATIVE_NEG` | Derivative |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

57270 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 15972 | 27.9% |
| EqualityElimination | 10874 | 19.0% |
| Transitivity | 7638 | 13.3% |
| Instantiation | 7250 | 12.7% |
| Reflexivity | 6504 | 11.4% |
| BetaStep | 3692 | 6.4% |
| Antisymmetry | 2896 | 5.1% |
| TypeInstantiation | 1724 | 3.0% |
| Assumption | 406 | 0.7% |
| Abstraction | 259 | 0.5% |
| Citation | 31 | 0.1% |
| Axiom | 12 | 0.0% |
| Definition | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !x:real. !y:real. x < y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (!z:real. x < z /\ z < y ==> (?u:real. derivative f z u)) ==> f x = f y ==> (?z:real. x < z /\ z < y /\ derivative f z 0)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find ROLLE"
```

From Scala it is `Derivative`'s, under the name `ROLLE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# MEAN_VALUE

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x < y \Rightarrow \left( \forall z \colon \mathbb{R}.\ x \le z \land z \le y \Rightarrow \operatorname{cont}(f, z) \right) \Rightarrow \left( \forall z \colon \mathbb{R}.\ x < z \land z < y \Rightarrow \left( \exists u \colon \mathbb{R}.\ \operatorname{deriv}(f, z, u) \right) \right) \Rightarrow \left( \exists z \colon \mathbb{R}.\ \exists u \colon \mathbb{R}.\ x < z \land z < y \land \operatorname{deriv}(f, z, u) \land f(y) - f(x) = u \cdot \left( y - x \right) \right)$$

```
!f:real -> real. !x:real. !y:real. x < y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (!z:real. x < z /\ z < y ==> (?u:real. derivative f z u)) ==> (?z:real. ?u:real. x < z /\ z < y /\ derivative f z u /\ f y - f x = u * (y - x))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 72 named facts in all.

| what | where |
|---|---|
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `CONTINUOUS_ATTAINS_MAX` | Continuity |
| `CONTINUOUS_ATTAINS_MIN` | Continuity |
| `CONTINUOUS_BOUNDED` | Continuity |
| `CONTINUOUS_ID` | Continuity |
| `CONTINUOUS_LINEAR` | Continuity |
| `CONTINUOUS_NEG` | Continuity |
| `INTERVAL_GLUING` | Continuity |
| `DERIVATIVE_ID` | Derivative |
| `DERIVATIVE_INTERIOR_MAX` | Derivative |
| `DERIVATIVE_INTERIOR_MIN` | Derivative |
| `DERIVATIVE_LINEAR` | Derivative |
| `DERIVATIVE_NEG` | Derivative |
| `DERIVATIVE_UNIQUE` | Derivative |
| `ROLLE` | Derivative |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_MUL` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `ABS_TRIANGLE` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_LE` | Order |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_OF_NOT_LE` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

122855 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 34710 | 28.3% |
| EqualityElimination | 22758 | 18.5% |
| Transitivity | 16666 | 13.6% |
| Instantiation | 16432 | 13.4% |
| Reflexivity | 13816 | 11.2% |
| BetaStep | 7611 | 6.2% |
| Antisymmetry | 6108 | 5.0% |
| TypeInstantiation | 3496 | 2.8% |
| Assumption | 759 | 0.6% |
| Abstraction | 438 | 0.4% |
| Citation | 37 | 0.0% |
| Axiom | 12 | 0.0% |
| Definition | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !x:real. !y:real. x < y ==> (!z:real. x <= z /\ z <= y ==> continuous f z) ==> (!z:real. x < z /\ z < y ==> (?u:real. derivative f z u)) ==> (?z:real. ?u:real. x < z /\ z < y /\ derivative f z u /\ f y - f x = u * (y - x))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find MEAN_VALUE"
```

From Scala it is `Derivative`'s, under the name `MEAN_VALUE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# INTEGRAL_DERIVATIVE_WITHIN

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall g \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ x \le y \Rightarrow \left( \forall z \colon \mathbb{R}.\ x \le z \land z \le y \Rightarrow \operatorname{deriv}_{[x, y]}(f, z, g(z)) \right) \Rightarrow \operatorname{integral}(g, x, y) = f(y) - f(x)$$

```
!f:real -> real. !g:real -> real. !x:real. !y:real. x <= y ==> (!z:real. x <= z /\ z <= y ==> derivative_within f x y z (g z)) ==> integral g x y = f y - f x
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 72 named facts in all.

| what | where |
|---|---|
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `INTERVAL_GLUING` | Continuity |
| `INDUCTIVE_INDUCT` | Inductive |
| `INDUCTIVE_INTRO` | Inductive |
| `FINE_SUM_EXISTS` | Integral |
| `FINE_SUM_GAUGE` | Integral |
| `FINE_SUM_INDUCT` | Integral |
| `FINE_SUM_JOIN` | Integral |
| `FINE_SUM_PIECE` | Integral |
| `HAS_INTEGRAL_DERIVATIVE_WITHIN` | Integral |
| `HAS_INTEGRAL_UNIQUE` | Integral |
| `INTEGRAL_UNIQUE` | Integral |
| `LE_BELOW_EVERY_POSITIVE` | Limit |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_OF_NONNEG` | Magnitude |
| `ABS_OF_NONPOS` | Magnitude |
| `ABS_ZERO` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `FST_PAIR` | Product |
| `PAIR_INJECTIVE` | Product |
| `PROD_REP_ABS` | Product |
| `PROD_REP_PAIR` | Product |
| `SND_PAIR` | Product |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

67633 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 21802 | 32.2% |
| EqualityElimination | 10425 | 15.4% |
| Instantiation | 9404 | 13.9% |
| Transitivity | 9398 | 13.9% |
| Reflexivity | 7277 | 10.8% |
| BetaStep | 3354 | 5.0% |
| Antisymmetry | 2759 | 4.1% |
| TypeInstantiation | 1664 | 2.5% |
| Abstraction | 815 | 1.2% |
| Assumption | 669 | 1.0% |
| Citation | 38 | 0.1% |
| Definition | 16 | 0.0% |
| Axiom | 12 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !g:real -> real. !x:real. !y:real. x <= y ==> (!z:real. x <= z /\ z <= y ==> derivative_within f x y z (g z)) ==> integral g x y = f y - f x"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find INTEGRAL_DERIVATIVE_WITHIN"
```

From Scala it is `Integral`'s, under the name `INTEGRAL_DERIVATIVE_WITHIN`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# DERIVATIVE_INTEGRAL

$$\forall f \colon \mathbb{R} \to \mathbb{R}.\ \forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ \forall z \colon \mathbb{R}.\ \left( \forall u \colon \mathbb{R}.\ x \le u \land u \le y \Rightarrow \operatorname{cont}(f, u) \right) \Rightarrow x < z \Rightarrow z < y \Rightarrow \operatorname{deriv}(\lambda u \colon \mathbb{R}.\ \operatorname{integral}(f, x, u), z, f(z))$$

```
!f:real -> real. !x:real. !y:real. !z:real. (!u:real. x <= u /\ u <= y ==> continuous f u) ==> x < z ==> z < y ==> derivative (\u:real. integral f x u) z (f z)
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

17 axioms reached, 16 of them named below, and 79 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `INTERVAL_GLUING` | Continuity |
| `DERIVATIVE_WITHIN_INTERIOR` | Derivative |
| `INDUCTIVE_INDUCT` | Inductive |
| `INDUCTIVE_INTRO` | Inductive |
| `CONTINUOUS_HAS_INTEGRAL` | Integral |
| `CONTINUOUS_INTEGRAL` | Integral |
| `DERIVATIVE_WITHIN_INTEGRAL` | Integral |
| `FINE_SUM_EXISTS` | Integral |
| `FINE_SUM_GAUGE` | Integral |
| `FINE_SUM_INDUCT` | Integral |
| `FINE_SUM_JOIN` | Integral |
| `FINE_SUM_PIECE` | Integral |
| `HAS_INTEGRAL_JOIN` | Integral |
| `HAS_INTEGRAL_UNIQUE` | Integral |
| `INTEGRAL_UNIQUE` | Integral |
| `LE_BELOW_EVERY_POSITIVE` | Limit |
| `ABS_ABOVE` | Magnitude |
| `ABS_ABOVE_NEG` | Magnitude |
| `ABS_CASES` | Magnitude |
| `ABS_NONNEG` | Magnitude |
| `ABS_ZERO` | Magnitude |
| `MAX_ABOVE_LEFT` | Magnitude |
| `MAX_ABOVE_RIGHT` | Magnitude |
| `MAX_CASES` | Magnitude |
| `MIN_BELOW_LEFT` | Magnitude |
| `MIN_BELOW_RIGHT` | Magnitude |
| `MIN_CASES` | Magnitude |
| `ADD_NONNEG` | Order |
| `ADD_NONNEG_LT` | Order |
| `ADD_POSITIVE` | Order |
| `CANCEL_NONNEG` | Order |
| `CANCEL_POSITIVE` | Order |
| `LE_ANTISYMMETRIC` | Order |
| `LE_CASES` | Order |
| `LE_FROM_ZERO` | Order |
| `LE_OF_EQ` | Order |
| `LE_OF_LT` | Order |
| `LE_TO_ZERO` | Order |
| `LT_FROM_ZERO` | Order |
| `LT_OF_NOT_LE` | Order |
| `LT_TO_ZERO` | Order |
| `MUL_NONNEG` | Order |
| `MUL_NONNEG_BOTH` | Order |
| `POSITIVE_NOT_ZERO` | Order |
| `ZERO_LT_ONE` | Order |
| `ADD_POSITIVE` | Positivity |
| `POSITIVE_NOT_ZERO` | Positivity |
| `ZERO_LT_ONE` | Positivity |
| `FST_PAIR` | Product |
| `PAIR_INJECTIVE` | Product |
| `PROD_REP_ABS` | Product |
| `PROD_REP_PAIR` | Product |
| `SND_PAIR` | Product |
| `ADD_ASSOC` | Real, assumed |
| `ADD_INVERSE` | Real, assumed |
| `ADD_SYM` | Real, assumed |
| `ADD_ZERO` | Real, assumed |
| `COMPLETENESS` | Real, assumed |
| `DISTRIBUTE` | Real, assumed |
| `LT_ADD` | Real, assumed |
| `LT_IRREFLEXIVE` | Real, assumed |
| `LT_MUL` | Real, assumed |
| `LT_TOTAL` | Real, assumed |
| `LT_TRANSITIVE` | Real, assumed |
| `MUL_ASSOC` | Real, assumed |
| `MUL_INVERSE` | Real, assumed |
| `MUL_ONE` | Real, assumed |
| `MUL_SYM` | Real, assumed |
| `ONE_NOT_ZERO` | Real, assumed |
| `BIT0` | Real, defined |
| `div` | Real, defined |
| `real_le` | Real, defined |
| `sub` | Real, defined |

1 axiom it reaches is not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

152276 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 51396 | 33.8% |
| EqualityElimination | 25410 | 16.7% |
| Instantiation | 18985 | 12.5% |
| Transitivity | 18681 | 12.3% |
| Reflexivity | 15774 | 10.4% |
| BetaStep | 7923 | 5.2% |
| Antisymmetry | 7061 | 4.6% |
| TypeInstantiation | 3964 | 2.6% |
| Assumption | 1521 | 1.0% |
| Abstraction | 1490 | 1.0% |
| Citation | 40 | 0.0% |
| Definition | 17 | 0.0% |
| Axiom | 14 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:real -> real. !x:real. !y:real. !z:real. (!u:real. x <= u /\ u <= y ==> continuous f u) ==> x < z ==> z < y ==> derivative (\u:real. integral f x u) z (f z)"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find DERIVATIVE_INTEGRAL"
```

From Scala it is `Integral`'s, under the name `DERIVATIVE_INTEGRAL`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

## Towards the incompleteness theorems

# NUM_BETA_SEQUENCE

$$\forall f \colon \mathbb{N} \to \mathbb{N}.\ \forall n \colon \mathbb{N}.\ \exists m \colon \mathbb{N}.\ \exists k \colon \mathbb{N}.\ \forall i \colon \mathbb{N}.\ i < n \Rightarrow \beta(m, k, i) = f(i)$$

```
!f:num -> num. !n:num. ?m:num. ?k:num. !i:num. i < n ==> NUM_BETA m k i = f i
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 107 named facts in all.

| what | where |
|---|---|
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BOUNDED_BELOW_LENGTH` | Coding |
| `NUM_CRT` | Coding |
| `NUM_CRT_PAIR` | Coding |
| `NUM_FACT_DIVIDES` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `NUM_GAUSS` | Coding |
| `NUM_GCD_MUL` | Coding |
| `NUM_GCD_PROD` | Coding |
| `NUM_GCD_SHIFTED_MULTIPLES` | Coding |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_POSITIVE` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_CONG_DIVISOR` | Modular |
| `NUM_CONG_ELIM` | Modular |
| `NUM_CONG_INTRO` | Modular |
| `NUM_CONG_TRANS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ANTISYM` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_DIVISION_UNIQUE` | Modular |
| `NUM_DIV_MOD` | Modular |
| `NUM_DIV_ZERO` | Modular |
| `NUM_GCD_DIVIDES` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_GCD_SYM` | Modular |
| `NUM_MOD_LT` | Modular |
| `NUM_MOD_OF_CONG` | Modular |
| `NUM_MOD_ZERO` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_LT_TRANS` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_PRE_LE` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_PRE_ZERO` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_LE` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

18200 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 6060 | 33.3% |
| EqualityElimination | 3619 | 19.9% |
| Reflexivity | 1704 | 9.4% |
| Instantiation | 1469 | 8.1% |
| Transitivity | 1386 | 7.6% |
| Antisymmetry | 1224 | 6.7% |
| BetaStep | 1122 | 6.2% |
| TypeInstantiation | 600 | 3.3% |
| Abstraction | 550 | 3.0% |
| Assumption | 402 | 2.2% |
| Citation | 50 | 0.3% |
| Definition | 13 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !f:num -> num. !n:num. ?m:num. ?k:num. !i:num. i < n ==> NUM_BETA m k i = f i"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_BETA_SEQUENCE"
```

From Scala it is `Coding`'s, under the name `NUM_BETA_SEQUENCE`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PA_FORM

$$\forall n \colon \mathbb{N}.\ \operatorname{PA}(n) \Rightarrow \operatorname{Fm}(n)$$

```
!n:num. NUM_PA n ==> NUM_FORM n
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 81 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_FORM_ALL` | Language |
| `NUM_FORM_CASES` | Language |
| `NUM_FORM_EQ` | Language |
| `NUM_FORM_IMP` | Language |
| `NUM_FORM_NOT` | Language |
| `NUM_PA_CASES` | Language |
| `NUM_SUBST_FORM_ALL` | Language |
| `NUM_SUBST_FORM_EQ` | Language |
| `NUM_SUBST_FORM_FORM` | Language |
| `NUM_SUBST_FORM_IMP` | Language |
| `NUM_SUBST_FORM_NOT` | Language |
| `NUM_SUBST_TERM_ADD` | Language |
| `NUM_SUBST_TERM_MUL` | Language |
| `NUM_SUBST_TERM_SUC` | Language |
| `NUM_SUBST_TERM_TERM` | Language |
| `NUM_SUBST_TERM_VAR` | Language |
| `NUM_SUBST_TERM_ZERO` | Language |
| `NUM_TERM_ADD` | Language |
| `NUM_TERM_CASES` | Language |
| `NUM_TERM_MUL` | Language |
| `NUM_TERM_SUC` | Language |
| `NUM_TERM_VAR` | Language |
| `NUM_TERM_ZERO` | Language |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_CODE_INJECTIVE` | Numbering |
| `NUM_CODE_LT_RIGHT` | Numbering |
| `NUM_FST_PAIR` | Numbering |
| `NUM_PAIR_INJECTIVE` | Numbering |
| `NUM_PAIR_LE_LEFT` | Numbering |
| `NUM_PAIR_LE_RIGHT` | Numbering |
| `NUM_PAYLOAD_CODE` | Numbering |
| `NUM_SND_PAIR` | Numbering |
| `NUM_TRI_MONOTONE` | Numbering |
| `NUM_TRI_SUC` | Numbering |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_BIT0_ADD` | Peano |
| `NUM_BIT1_SUC` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_LT_TRANS` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_LE_TRANS` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_ONE_SUC` | Peano |
| `NUM_STRONG_INDUCTION` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

38400 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 13385 | 34.9% |
| EqualityElimination | 7519 | 19.6% |
| Reflexivity | 3514 | 9.2% |
| Instantiation | 3199 | 8.3% |
| Transitivity | 2711 | 7.1% |
| Antisymmetry | 2686 | 7.0% |
| BetaStep | 2205 | 5.7% |
| TypeInstantiation | 1225 | 3.2% |
| Abstraction | 997 | 2.6% |
| Assumption | 923 | 2.4% |
| Citation | 22 | 0.1% |
| Definition | 13 | 0.0% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. NUM_PA n ==> NUM_FORM n"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PA_FORM"
```

From Scala it is `Language`'s, under the name `NUM_PA_FORM`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PROV_MP

$$\forall n \colon \mathbb{N}.\ \forall m \colon \mathbb{N}.\ \operatorname{Prov}(\lceil 7, \langle n, m \rangle \rceil) \Rightarrow \operatorname{Prov}(n) \Rightarrow \operatorname{Prov}(m)$$

```
!n:num. !m:num. NUM_PROV (NUM_CODE 7 (NUM_PAIR n m)) ==> NUM_PROV n ==> NUM_PROV m
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 121 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BETA_SEQUENCE` | Coding |
| `NUM_BOUNDED_BELOW_LENGTH` | Coding |
| `NUM_CRT` | Coding |
| `NUM_CRT_PAIR` | Coding |
| `NUM_FACT_DIVIDES` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `NUM_GAUSS` | Coding |
| `NUM_GCD_MUL` | Coding |
| `NUM_GCD_PROD` | Coding |
| `NUM_GCD_SHIFTED_MULTIPLES` | Coding |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_POSITIVE` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_CONG_DIVISOR` | Modular |
| `NUM_CONG_ELIM` | Modular |
| `NUM_CONG_INTRO` | Modular |
| `NUM_CONG_TRANS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ANTISYM` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_DIVISION_UNIQUE` | Modular |
| `NUM_DIV_MOD` | Modular |
| `NUM_DIV_ZERO` | Modular |
| `NUM_GCD_DIVIDES` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_GCD_SYM` | Modular |
| `NUM_MOD_LT` | Modular |
| `NUM_MOD_OF_CONG` | Modular |
| `NUM_MOD_ZERO` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_LE_CANCEL` | Peano |
| `NUM_ADD_LT_MONOTONE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_LT_TRANS` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_LE_TRANS` | Peano |
| `NUM_LT_NOT_LE` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_PRE_LE` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_PRE_ZERO` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_LE` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `NUM_PROOF_CASES` | Provability |
| `NUM_PROV_CASES` | Provability |
| `NUM_STEP_CASES` | Provability |
| `NUM_STEP_SHIFT` | Provability |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

6579 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| EqualityElimination | 1640 | 24.9% |
| Congruence | 1490 | 22.6% |
| Reflexivity | 738 | 11.2% |
| Instantiation | 596 | 9.1% |
| Antisymmetry | 563 | 8.6% |
| Transitivity | 489 | 7.4% |
| BetaStep | 478 | 7.3% |
| TypeInstantiation | 283 | 4.3% |
| Assumption | 194 | 2.9% |
| Abstraction | 76 | 1.2% |
| Citation | 22 | 0.3% |
| Definition | 10 | 0.2% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. !m:num. NUM_PROV (NUM_CODE 7 (NUM_PAIR n m)) ==> NUM_PROV n ==> NUM_PROV m"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PROV_MP"
```

From Scala it is `Provability`'s, under the name `NUM_PROV_MP`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_PROV_SELF

$$\forall n \colon \mathbb{N}.\ \operatorname{Fm}(n) \Rightarrow \operatorname{Prov}(\lceil 7, \langle n, n \rangle \rceil)$$

```
!n:num. NUM_FORM n ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR n n))
```

*The formula above is set for reading and **does not read back**. The line under it is the text the page was generated from: that is the one to compare against a source, or to paste into `Ask`.*

## What it rests on

2 axioms reached, 0 of them named below, and 132 named facts in all.

| what | where |
|---|---|
| `COND` | Classical, defined |
| `COND_FALSE` | Classical, derived |
| `COND_TRUE` | Classical, derived |
| `DOUBLE_NEGATION` | Classical, derived |
| `EXCLUDED_MIDDLE` | Classical, derived |
| `TRUTH_NOT_FALSITY` | Classical, derived |
| `NUM_BETA_SEQUENCE` | Coding |
| `NUM_BOUNDED_BELOW_LENGTH` | Coding |
| `NUM_CRT` | Coding |
| `NUM_CRT_PAIR` | Coding |
| `NUM_FACT_DIVIDES` | Coding |
| `NUM_FACT_POSITIVE` | Coding |
| `NUM_FACT_SUC` | Coding |
| `NUM_FACT_ZERO` | Coding |
| `NUM_GAUSS` | Coding |
| `NUM_GCD_MUL` | Coding |
| `NUM_GCD_PROD` | Coding |
| `NUM_GCD_SHIFTED_MULTIPLES` | Coding |
| `NUM_PROD_DIVIDES` | Coding |
| `NUM_PROD_POSITIVE` | Coding |
| `NUM_PROD_SUC` | Coding |
| `NUM_PROD_ZERO` | Coding |
| `NUM_FORM_CASES` | Language |
| `NUM_FORM_IMP` | Language |
| `NUM_LOGIC_CASES` | Language |
| `NUM_LOGIC_DISTRIBUTE` | Language |
| `NUM_LOGIC_WEAKEN` | Language |
| `NUM_BEZOUT` | Modular |
| `NUM_BEZOUT_EXISTS` | Modular |
| `NUM_CONG_DIVISOR` | Modular |
| `NUM_CONG_ELIM` | Modular |
| `NUM_CONG_INTRO` | Modular |
| `NUM_CONG_TRANS` | Modular |
| `NUM_DIVIDES_ADD` | Modular |
| `NUM_DIVIDES_ANTISYM` | Modular |
| `NUM_DIVIDES_ELIM` | Modular |
| `NUM_DIVIDES_INTRO` | Modular |
| `NUM_DIVIDES_LE` | Modular |
| `NUM_DIVIDES_MUL` | Modular |
| `NUM_DIVIDES_ONE` | Modular |
| `NUM_DIVIDES_REFL` | Modular |
| `NUM_DIVIDES_SUMMAND` | Modular |
| `NUM_DIVIDES_TRANS` | Modular |
| `NUM_DIVIDES_ZERO` | Modular |
| `NUM_DIVISION` | Modular |
| `NUM_DIVISION_UNIQUE` | Modular |
| `NUM_DIV_MOD` | Modular |
| `NUM_DIV_ZERO` | Modular |
| `NUM_GCD_DIVIDES` | Modular |
| `NUM_GCD_DIVIDES_LEFT` | Modular |
| `NUM_GCD_DIVIDES_RIGHT` | Modular |
| `NUM_GCD_GREATEST` | Modular |
| `NUM_GCD_SYM` | Modular |
| `NUM_MOD_LT` | Modular |
| `NUM_MOD_OF_CONG` | Modular |
| `NUM_MOD_ZERO` | Modular |
| `NUM_ONE_DIVIDES` | Modular |
| `NUM_ZERO_DIVIDES` | Modular |
| `IND_SUC_0` | Natural |
| `NUM_ABS_REP` | Natural |
| `NUM_CASES` | Natural |
| `NUM_INDUCTION` | Natural |
| `NUM_REP_0` | Natural |
| `NUM_REP_ABS` | Natural |
| `NUM_REP_DEST` | Natural |
| `NUM_REP_SUC` | Natural |
| `NUM_SUC_INJECTIVE` | Natural |
| `NUM_SUC_NOT_ZERO` | Natural |
| `NUM_CODE_LT_RIGHT` | Numbering |
| `NUM_PAIR_LE_LEFT` | Numbering |
| `NUM_PAIR_LE_RIGHT` | Numbering |
| `NUM_TRI_SUC` | Numbering |
| `NUM_ADD_ASSOC` | Peano |
| `NUM_ADD_CANCEL` | Peano |
| `NUM_ADD_CANCEL_LEFT` | Peano |
| `NUM_ADD_EQ_ZERO` | Peano |
| `NUM_ADD_EXCHANGE` | Peano |
| `NUM_ADD_LE_CANCEL` | Peano |
| `NUM_ADD_LT_MONOTONE` | Peano |
| `NUM_ADD_MONOTONE` | Peano |
| `NUM_ADD_SHIFT` | Peano |
| `NUM_ADD_SUB` | Peano |
| `NUM_ADD_SUC` | Peano |
| `NUM_ADD_SYM` | Peano |
| `NUM_ADD_ZERO` | Peano |
| `NUM_GREATEST` | Peano |
| `NUM_LEAST` | Peano |
| `NUM_LE_ADD` | Peano |
| `NUM_LE_ANTISYM` | Peano |
| `NUM_LE_CASES` | Peano |
| `NUM_LE_LT_TRANS` | Peano |
| `NUM_LE_OF_LT` | Peano |
| `NUM_LE_REFL` | Peano |
| `NUM_LE_SUC` | Peano |
| `NUM_LE_TOTAL` | Peano |
| `NUM_LE_TRANS` | Peano |
| `NUM_LE_ZERO` | Peano |
| `NUM_LT_IRREFL` | Peano |
| `NUM_LT_LE_TRANS` | Peano |
| `NUM_LT_NOT_LE` | Peano |
| `NUM_LT_SUC` | Peano |
| `NUM_LT_SUC_CASES` | Peano |
| `NUM_LT_TOTAL` | Peano |
| `NUM_LT_TRANS` | Peano |
| `NUM_MUL_ASSOC` | Peano |
| `NUM_MUL_DISTRIBUTE` | Peano |
| `NUM_MUL_POSITIVE` | Peano |
| `NUM_MUL_SUC` | Peano |
| `NUM_MUL_SYM` | Peano |
| `NUM_MUL_ZERO` | Peano |
| `NUM_NOT_LT_ZERO` | Peano |
| `NUM_PRE_LE` | Peano |
| `NUM_PRE_SUC` | Peano |
| `NUM_PRE_ZERO` | Peano |
| `NUM_SUB_ADD` | Peano |
| `NUM_SUB_LE` | Peano |
| `NUM_SUB_SUC` | Peano |
| `NUM_SUB_SUC_SUC` | Peano |
| `NUM_SUB_ZERO` | Peano |
| `NUM_SUC_ADD` | Peano |
| `NUM_SUC_MUL` | Peano |
| `NUM_SUC_NOT_SELF` | Peano |
| `NUM_ZERO_ADD` | Peano |
| `NUM_ZERO_LE` | Peano |
| `NUM_ZERO_LT_SUC` | Peano |
| `NUM_ZERO_MUL` | Peano |
| `NUM_PROOF_CASES` | Provability |
| `NUM_PROV_CASES` | Provability |
| `NUM_PROV_LOGIC` | Provability |
| `NUM_PROV_MP` | Provability |
| `NUM_STEP_CASES` | Provability |
| `NUM_STEP_SHIFT` | Provability |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

557 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 127 | 22.8% |
| EqualityElimination | 119 | 21.4% |
| Transitivity | 65 | 11.7% |
| Reflexivity | 59 | 10.6% |
| BetaStep | 49 | 8.8% |
| Antisymmetry | 40 | 7.2% |
| Instantiation | 37 | 6.6% |
| Abstraction | 26 | 4.7% |
| TypeInstantiation | 17 | 3.1% |
| Assumption | 9 | 1.6% |
| Citation | 5 | 0.9% |
| Definition | 4 | 0.7% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !n:num. NUM_FORM n ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR n n))"
```

The claim is **not** quoted: `sbt` hands the arguments over already split, so the
shell's quotes are gone before the command sees them.

**A refusal here is not evidence against the theorem.** The surface decides a few fragments and chains library lemmas for the rest, so a theorem obtained by a hand derivation is one it can refuse, and what it prints then is the obstacle it met rather than a verdict on the claim. In particular an assignment like `P x := true, Q x := false` is a countermodel of the claim's **propositional skeleton**, whose atoms are uninterpreted: `!x:real. 1 < x ==> 0 < x \/ x = 99` is true and produces one. The theorem is the one the kernel holds, counted above, and the two routes below reach it whatever this one answers.

Look it up instead, by name or by shape:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Find NUM_PROV_SELF"
```

From Scala it is `Deduction`'s, under the name `NUM_PROV_SELF`. Specialise it with `Rules.specTo`, which takes the instance wanted and finds the instantiation by matching: the order the binders were written in is not part of any contract here.

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk, which stops at a published
  fact: the fact's own proof was checked when its development was built.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

<!-- end generated: examples -->
