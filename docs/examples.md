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
| Analysis | **partly here, since 2026-09-15.** `Limit` declares `converges` and `lim`, `Transcendental` declares `exp`, `sin`, `cos`, `ln`, `sinh` and `cosh` as their power series through that limit, and between them they cost no axiom. Proved over them: the value of each function at zero, that a limit is unique, the monotone convergence theorem, which is where `COMPLETENESS` is read a second time and the first thing here that obtains a limit rather than assuming one, the comparison test, and since 2026-09-16 the two facts that say where a limit obtained that way sits, `CONVERGES_LE` and `CONVERGES_GE` | The comparison test is spent on the geometric series at one half, whose limit `LimitSpec` puts between zero and two, and since 2026-09-20 on the exponential: `2 < exp 1` is `EXP_ONE_ABOVE_TWO`, the first fact here about a value the system does not compute, and the rung it waited on was arithmetic rather than analysis, `2^i <= 2 * i!` on `num`. Since 2026-09-21 the Cauchy product is proved, and with it `exp (x + y) = exp x * exp y` and the hyperbolic identity `cosh x * cosh x - sinh x * sinh x = 1`; and since 2026-09-24 `Root` declares `sqrt` and proves it exists, which is `COMPLETENESS` read a third time. Since 2026-09-24 the trigonometric identity is `SIN_COS_SQUARED`, which is not the hyperbolic one with symbols changed: `sin` and `cos` meet `exp` only through a square root of minus one, so it is the Cauchy product at their own series. The same day `Continuity` defined continuity at a point and proved the intermediate value theorem from `COMPLETENESS`; `Logarithm` then proves the exponential continuous and onto the positive reals, which gives `ln` its first facts. Since 2026-09-25 a function continuous on `[a, b]` is bounded there and takes a greatest and a least value, `CONTINUOUS_ATTAINS_MAX` and `CONTINUOUS_ATTAINS_MIN`, both through one compactness lemma, `INTERVAL_GLUING`. No derivative and no integral. **Nothing primitive is missing** here either: each of those is expressible over the theory as it stands |
| The fundamental theorem of algebra | **out of reach, and nothing about it is a decision** | It wants the complex numbers, so it wants the reals as a construction with the integers and the rationals under them, which `docs/adr/0007` puts in that order and which has not started. Then it wants an argument of its own: the route through Liouville wants a derivative, the route through winding numbers wants a topology, and neither exists here. Unlike the four colour theorem below it, what stands in the way is work rather than a recorded decision |
| The fundamental theorem of calculus | **out of reach, and the nearer of the two** | Continuity is defined since 2026-09-24 and the intermediate value theorem is proved; the derivative and the integral are not defined, and both are expressible over the reals as they are axiomatised today: this one does **not** wait on the construction, which is the difference from the row above. What it waits on is a derivative and then an integral. It is the entry on this table most likely to move next |
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

$$\forall x \colon \mathbb{N}.\ \exists y \colon \mathbb{N}.\ \mathrm{prime}(y) \land x < y$$

```
!x:num. ?y:num. NUM_PRIME y /\ x < y
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. ?y:num. NUM_PRIME y /\ x < y"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ 0 < y \Rightarrow \lnot \left( x \cdot x = \mathrm{suc}(\mathrm{suc}(0)) \cdot \left( y \cdot y \right) \right)$$

```
!x:num. !y:num. 0 < y ==> ~(x * x = SUC (SUC 0) * (y * y))
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. 0 < y ==> ~(x * x = SUC (SUC 0) * (y * y))"
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

$$\forall x \colon \mathbb{N}.\ \mathrm{suc}(0) < x \Rightarrow \left( \exists y \colon \mathbb{N}.\ \mathrm{prime}(y) \land y \mid x \right)$$

```
!x:num. SUC 0 < x ==> (?y:num. NUM_PRIME y /\ NUM_DIVIDES y x)
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. SUC 0 < x ==> (?y:num. NUM_PRIME y /\ NUM_DIVIDES y x)"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \lnot \left( x = 0 \right) \lor \lnot \left( y = 0 \right) \Rightarrow \left( \exists z \colon \mathbb{N}.\ \exists u \colon \mathbb{N}.\ x \cdot z = y \cdot u + \gcd(x, y) \lor y \cdot z = x \cdot u + \gcd(x, y) \right)$$

```
!x:num. !y:num. ~(x = 0) \/ ~(y = 0) ==> (?z:num. ?u:num. x * z = y * u + NUM_GCD x y \/ y * z = x * u + NUM_GCD x y)
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

9098 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2337 | 25.7% |
| EqualityElimination | 2112 | 23.2% |
| Instantiation | 884 | 9.7% |
| Reflexivity | 867 | 9.5% |
| Antisymmetry | 812 | 8.9% |
| Transitivity | 617 | 6.8% |
| BetaStep | 547 | 6.0% |
| TypeInstantiation | 360 | 4.0% |
| Assumption | 324 | 3.6% |
| Abstraction | 197 | 2.2% |
| Citation | 28 | 0.3% |
| Definition | 12 | 0.1% |
| Axiom | 1 | 0.0% |

## How to get it

Put the claim to the prover, which puts it to the whole tactic surface:

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. ~(x = 0) \/ ~(y = 0) ==> (?z:num. ?u:num. x * z = y * u + NUM_GCD x y \/ y * z = x * u + NUM_GCD x y)"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \forall z \colon \mathbb{N}.\ \mathrm{prime}(x) \Rightarrow x \mid y \cdot z \Rightarrow x \mid y \lor x \mid z$$

```
!x:num. !y:num. !z:num. NUM_PRIME x ==> NUM_DIVIDES x (y * z) ==> NUM_DIVIDES x y \/ NUM_DIVIDES x z
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

10271 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2591 | 25.2% |
| EqualityElimination | 2395 | 23.3% |
| Instantiation | 1024 | 10.0% |
| Reflexivity | 989 | 9.6% |
| Antisymmetry | 925 | 9.0% |
| Transitivity | 713 | 6.9% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. !z:num. NUM_PRIME x ==> NUM_DIVIDES x (y * z) ==> NUM_DIVIDES x y \/ NUM_DIVIDES x z"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \mathrm{prime}(x) \Rightarrow y \mid x \Rightarrow y = \mathrm{suc}(0) \lor y = x$$

```
!x:num. !y:num. NUM_PRIME x ==> NUM_DIVIDES y x ==> y = SUC 0 \/ y = x
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. NUM_PRIME x ==> NUM_DIVIDES y x ==> y = SUC 0 \/ y = x"
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

$$\forall x \colon \mathbb{N}.\ \mathrm{suc}(0) < x \Rightarrow \left( \exists y \colon \mathbb{N} \to \mathbb{N}.\ \exists z \colon \mathbb{N}.\ 0 < z \land \left( \forall u \colon \mathbb{N}.\ u < z \Rightarrow \mathrm{prime}(y(u)) \right) \land \left( \forall u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ u < v \land v < z \Rightarrow y(u) \le y(v) \right) \land \prod_{i < z} y(i) = x \right)$$

```
!x:num. SUC 0 < x ==> (?y:num -> num. ?z:num. 0 < z /\ (!u:num. u < z ==> NUM_PRIME (y u)) /\ (!u:num. !v:num. u < v /\ v < z ==> y u <= y v) /\ NUM_PROD y z = x)
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. SUC 0 < x ==> (?y:num -> num. ?z:num. 0 < z /\ (!u:num. u < z ==> NUM_PRIME (y u)) /\ (!u:num. !v:num. u < v /\ v < z ==> y u <= y v) /\ NUM_PROD y z = x)"
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

$$\forall x \colon \mathbb{N} \to \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \forall z \colon \mathbb{N} \to \mathbb{N}.\ \forall u \colon \mathbb{N}.\ \left( \forall v \colon \mathbb{N}.\ v < y \Rightarrow \mathrm{prime}(x(v)) \right) \Rightarrow \left( \forall v \colon \mathbb{N}.\ \forall w \colon \mathbb{N}.\ v < w \land w < y \Rightarrow x(v) \le x(w) \right) \Rightarrow \left( \forall v \colon \mathbb{N}.\ v < u \Rightarrow \mathrm{prime}(z(v)) \right) \Rightarrow \left( \forall v \colon \mathbb{N}.\ \forall w \colon \mathbb{N}.\ v < w \land w < u \Rightarrow z(v) \le z(w) \right) \Rightarrow \prod_{i < y} x(i) = \prod_{i < u} z(i) \Rightarrow y = u \land \left( \forall v \colon \mathbb{N}.\ v < y \Rightarrow x(v) = z(v) \right)$$

```
!x:num -> num. !y:num. !z:num -> num. !u:num. (!v:num. v < y ==> NUM_PRIME (x v)) ==> (!v:num. !w:num. v < w /\ w < y ==> x v <= x w) ==> (!v:num. v < u ==> NUM_PRIME (z v)) ==> (!v:num. !w:num. v < w /\ w < u ==> z v <= z w) ==> NUM_PROD x y = NUM_PROD z u ==> y = u /\ (!v:num. v < y ==> x v = z v)
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

5976 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 1821 | 30.5% |
| EqualityElimination | 1311 | 21.9% |
| Reflexivity | 564 | 9.4% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num -> num. !y:num. !z:num -> num. !u:num. (!v:num. v < y ==> NUM_PRIME (x v)) ==> (!v:num. !w:num. v < w /\ w < y ==> x v <= x w) ==> (!v:num. v < u ==> NUM_PRIME (z v)) ==> (!v:num. !w:num. v < w /\ w < u ==> z v <= z w) ==> NUM_PROD x y = NUM_PROD z u ==> y = u /\ (!v:num. v < y ==> x v = z v)"
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

$$\forall x \colon \mathbb{N} \to \mathbb{N}.\ \forall y \colon \mathbb{N} \to \mathbb{N}.\ \forall z \colon \mathbb{N}.\ \left( \forall u \colon \mathbb{N}.\ u < z \Rightarrow 0 < x(u) \right) \Rightarrow \left( \forall u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ u < z \land v < z \land \lnot \left( u = v \right) \Rightarrow \gcd(x(u), x(v)) = \mathrm{suc}(0) \right) \Rightarrow \left( \exists u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ v < z \Rightarrow u \equiv y(v) \pmod{x(v)} \right)$$

```
!x:num -> num. !y:num -> num. !z:num. (!u:num. u < z ==> 0 < x u) ==> (!u:num. !v:num. u < z /\ v < z /\ ~(u = v) ==> NUM_GCD (x u) (x v) = SUC 0) ==> (?u:num. !v:num. v < z ==> NUM_CONG (x v) u (y v))
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

11373 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 4180 | 36.8% |
| EqualityElimination | 2025 | 17.8% |
| Reflexivity | 976 | 8.6% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num -> num. !y:num -> num. !z:num. (!u:num. u < z ==> 0 < x u) ==> (!u:num. !v:num. u < z /\ v < z /\ ~(u = v) ==> NUM_GCD (x u) (x v) = SUC 0) ==> (?u:num. !v:num. v < z ==> NUM_CONG (x v) u (y v))"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ 0 < x \land x \le y \Rightarrow x \mid y!$$

```
!x:num. !y:num. 0 < x /\ x <= y ==> NUM_DIVIDES x (NUM_FACT y)
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

4503 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2062 | 45.8% |
| EqualityElimination | 612 | 13.6% |
| Abstraction | 329 | 7.3% |
| Transitivity | 308 | 6.8% |
| Reflexivity | 280 | 6.2% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. 0 < x /\ x <= y ==> NUM_DIVIDES x (NUM_FACT y)"
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

$$\forall x \colon \mathbb{N} \to \mathbb{B}.\ \left( \forall y \colon \mathbb{N}.\ \left( \forall z \colon \mathbb{N}.\ z < y \Rightarrow x(z) \right) \Rightarrow x(y) \right) \Rightarrow \left( \forall y \colon \mathbb{N}.\ x(y) \right)$$

```
!x:num -> bool. (!y:num. (!z:num. z < y ==> x z) ==> x y) ==> (!y:num. x y)
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

5358 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2236 | 41.7% |
| EqualityElimination | 832 | 15.5% |
| Reflexivity | 360 | 6.7% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num -> bool. (!y:num. (!z:num. z < y ==> x z) ==> x y) ==> (!y:num. x y)"
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

$$\forall x \colon \mathbb{R}.\ \exists y \colon \mathbb{N}.\ x < y_{\mathbb{R}}$$

```
!x:real. ?y:num. x < real_of_num y
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

11324 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 3962 | 35.0% |
| EqualityElimination | 1972 | 17.4% |
| Transitivity | 1161 | 10.3% |
| Reflexivity | 1104 | 9.7% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. ?y:num. x < real_of_num y"
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

## Towards the incompleteness theorems

# NUM_BETA_SEQUENCE

$$\forall x \colon \mathbb{N} \to \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \exists z \colon \mathbb{N}.\ \exists u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ v < y \Rightarrow \beta(z, u, v) = x(v)$$

```
!x:num -> num. !y:num. ?z:num. ?u:num. !v:num. v < y ==> NUM_BETA z u v = x v
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

18203 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 6060 | 33.3% |
| EqualityElimination | 3619 | 19.9% |
| Reflexivity | 1707 | 9.4% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num -> num. !y:num. ?z:num. ?u:num. !v:num. v < y ==> NUM_BETA z u v = x v"
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

$$\forall x \colon \mathbb{N}.\ \operatorname{PA}(x) \Rightarrow \operatorname{Fm}(x)$$

```
!x:num. NUM_PA x ==> NUM_FORM x
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

38404 inferences of its own, a published fact it uses counting as one `Citation`. The account above describes them and is not a second proof: what the kernel checked for this proof is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 13385 | 34.9% |
| EqualityElimination | 7519 | 19.6% |
| Reflexivity | 3518 | 9.2% |
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. NUM_PA x ==> NUM_FORM x"
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

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \operatorname{Prov}(\lceil 7, \langle x, y \rangle \rceil) \Rightarrow \operatorname{Prov}(x) \Rightarrow \operatorname{Prov}(y)$$

```
!x:num. !y:num. NUM_PROV (NUM_CODE 7 (NUM_PAIR x y)) ==> NUM_PROV x ==> NUM_PROV y
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. NUM_PROV (NUM_CODE 7 (NUM_PAIR x y)) ==> NUM_PROV x ==> NUM_PROV y"
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

$$\forall x \colon \mathbb{N}.\ \operatorname{Fm}(x) \Rightarrow \operatorname{Prov}(\lceil 7, \langle x, x \rangle \rceil)$$

```
!x:num. NUM_FORM x ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR x x))
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
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. NUM_FORM x ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR x x))"
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
