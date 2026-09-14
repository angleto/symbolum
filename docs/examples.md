# What this system has proved

A dozen results, each printed as its own page: the statement as the kernel holds it, what the proof
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
| Number theory over `num` | **partly here.** Bezout, Euclid's lemma, division with remainder, congruences, the gcd, the Chinese remainder theorem, the factorial | Unique factorisation is the next rung and every piece of it exists. What blocks it is the **statement**: uniqueness is a claim about a multiset of primes, and this system has no lists, no finite sets and no multisets |
| The incompleteness theorems | **in progress.** The object language, both axiom sets, the proof predicate, closure under both rules of inference, and the first derivations of the embedded theory | `Prov` as a formula **of the object language** does not exist; what exists is `NUM_PROV`, a predicate of the ambient logic. D1, D2 and D3 are statements about that formula, so none of the three can be stated yet. `docs/adr/0013` is the plan |
| Analysis | **nothing.** The reals are a complete ordered field with `abs`, and `COMPLETENESS` is read by exactly one theorem | No limit, no sequence of reals, no continuity, no derivative, no integral. **Nothing primitive is missing**: the definitions are expressible over the theory as it stands, and this is the largest piece of work on this table that is not blocked on anything but work |
| The four colour theorem | **out of reach, and not only by size** | It needs graphs and finite sets, which do not exist, and the only proof anyone has runs a computation over 633 configurations. `docs/adr/0010` decides there is **no computing rule in the kernel** and that there will not be one while the trusted base is the argument, so the route Gonthier took is closed here by a recorded decision rather than by effort |
| Hilbert's solved problems | **out of reach, with one exception worth naming** | Most need machinery nothing here is near. The tenth, Matiyasevich's theorem, is the exception: it is a statement about Diophantine definability, and the beta function, the coding of sequences and the arithmetisation of syntax that the incompleteness work is building are the same ground floor. It is the one entry on this list that the current work walks towards rather than away from |

Two things this table is careful about. **"Nothing primitive is missing" and "it is a lot of work"
are different statements**, and analysis is the first and not the second kind of gap, while the four
colour theorem is neither: it is blocked by a decision that was taken deliberately and written down.
And **a rung that is reachable is not thereby cheap.** The entries marked partly here each took days
of work per theorem, and nothing below suggests the next one will be faster.

<!-- generated: examples, do not edit below this line -->

## Number theory

# NUM_BEZOUT

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \lnot \left( x = 0 \right) \lor \lnot \left( y = 0 \right) \Rightarrow \left( \exists z \colon \mathbb{N}.\ \exists u \colon \mathbb{N}.\ x \cdot z = y \cdot u + \gcd(x, y) \lor y \cdot z = x \cdot u + \gcd(x, y) \right)$$

```
!x:num. !y:num. ~(x = 0) \/ ~(y = 0) ==> (?z:num. ?u:num. NUM_MUL x z = NUM_ADD (NUM_MUL y u) (NUM_GCD x y) \/ NUM_MUL y z = NUM_ADD (NUM_MUL x u) (NUM_GCD x y))
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

24296 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 7672 | 31.6% |
| EqualityElimination | 5026 | 20.7% |
| Instantiation | 2081 | 8.6% |
| Reflexivity | 2014 | 8.3% |
| Antisymmetry | 1978 | 8.1% |
| Transitivity | 1673 | 6.9% |
| BetaStep | 1393 | 5.7% |
| TypeInstantiation | 831 | 3.4% |
| Abstraction | 806 | 3.3% |
| Assumption | 799 | 3.3% |
| Definition | 19 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_EUCLID

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \forall z \colon \mathbb{N}.\ \mathrm{prime}(x) \Rightarrow x \mid y \cdot z \Rightarrow x \mid y \lor x \mid z$$

```
!x:num. !y:num. !z:num. NUM_PRIME x ==> NUM_DIVIDES x (NUM_MUL y z) ==> NUM_DIVIDES x y \/ NUM_DIVIDES x z
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

25466 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 7926 | 31.1% |
| EqualityElimination | 5309 | 20.8% |
| Instantiation | 2221 | 8.7% |
| Reflexivity | 2135 | 8.4% |
| Antisymmetry | 2091 | 8.2% |
| Transitivity | 1769 | 6.9% |
| BetaStep | 1463 | 5.7% |
| TypeInstantiation | 874 | 3.4% |
| Assumption | 840 | 3.3% |
| Abstraction | 814 | 3.2% |
| Definition | 20 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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

215 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

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

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_CRT

$$\forall x \colon \mathbb{N} \to \mathbb{N}.\ \forall y \colon \mathbb{N} \to \mathbb{N}.\ \forall z \colon \mathbb{N}.\ \left( \forall u \colon \mathbb{N}.\ u < z \Rightarrow 0 < x(u) \right) \Rightarrow \left( \forall u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ u < z \land v < z \land \lnot \left( u = v \right) \Rightarrow \gcd(x(u), x(v)) = \mathrm{suc}(0) \right) \Rightarrow \left( \exists u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ v < z \Rightarrow u \equiv y(v) \pmod{x(v)} \right)$$

```
!x:num -> num. !y:num -> num. !z:num. (!u:num. NUM_LT u z ==> NUM_LT 0 (x u)) ==> (!u:num. !v:num. NUM_LT u z /\ NUM_LT v z /\ ~(u = v) ==> NUM_GCD (x u) (x v) = SUC 0) ==> (?u:num. !v:num. NUM_LT v z ==> NUM_CONG (x v) u (y v))
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

37312 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 11540 | 30.9% |
| EqualityElimination | 7781 | 20.9% |
| Instantiation | 3290 | 8.8% |
| Reflexivity | 3255 | 8.7% |
| Antisymmetry | 2949 | 7.9% |
| Transitivity | 2697 | 7.2% |
| BetaStep | 2201 | 5.9% |
| TypeInstantiation | 1312 | 3.5% |
| Assumption | 1155 | 3.1% |
| Abstraction | 1105 | 3.0% |
| Definition | 23 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

# NUM_FACT_DIVIDES

$$\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ 0 < x \land x \le y \Rightarrow x \mid y!$$

```
!x:num. !y:num. NUM_LT 0 x /\ NUM_LE x y ==> NUM_DIVIDES x (NUM_FACT y)
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

13106 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 4883 | 37.3% |
| EqualityElimination | 2299 | 17.5% |
| Transitivity | 1034 | 7.9% |
| Reflexivity | 1008 | 7.7% |
| Instantiation | 913 | 7.0% |
| Antisymmetry | 827 | 6.3% |
| BetaStep | 777 | 5.9% |
| Abstraction | 613 | 4.7% |
| TypeInstantiation | 392 | 3.0% |
| Assumption | 337 | 2.6% |
| Definition | 19 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

---

## The naturals, and what separates the reals from an ordered field

# NUM_STRONG_INDUCTION

$$\forall x \colon \mathbb{N} \to \mathbb{B}.\ \left( \forall y \colon \mathbb{N}.\ \left( \forall z \colon \mathbb{N}.\ z < y \Rightarrow x(z) \right) \Rightarrow x(y) \right) \Rightarrow \left( \forall y \colon \mathbb{N}.\ x(y) \right)$$

```
!x:num -> bool. (!y:num. (!z:num. NUM_LT z y ==> x z) ==> x y) ==> (!y:num. x y)
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

6794 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 2629 | 38.7% |
| EqualityElimination | 1133 | 16.7% |
| Antisymmetry | 486 | 7.2% |
| Reflexivity | 484 | 7.1% |
| Transitivity | 462 | 6.8% |
| Instantiation | 452 | 6.7% |
| Abstraction | 410 | 6.0% |
| BetaStep | 348 | 5.1% |
| Assumption | 202 | 3.0% |
| TypeInstantiation | 168 | 2.5% |
| Definition | 16 | 0.2% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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
| `le` | Real, defined |
| `sub` | Real, defined |

2 axioms it reaches are not named above: `Library.of` holds no classical axiom, and says in its own comment why.

## The derivation

Not recorded. The development that proved this has not been converted to record its steps,
so the page can say what the theorem rests on and what it cost and cannot say how it was
obtained.

## The proof the kernel holds

15513 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 4940 | 31.8% |
| EqualityElimination | 2933 | 18.9% |
| Transitivity | 1530 | 9.9% |
| Reflexivity | 1497 | 9.6% |
| Instantiation | 1475 | 9.5% |
| BetaStep | 926 | 6.0% |
| Antisymmetry | 856 | 5.5% |
| TypeInstantiation | 521 | 3.4% |
| Abstraction | 483 | 3.1% |
| Assumption | 317 | 2.0% |
| Axiom | 17 | 0.1% |
| Definition | 16 | 0.1% |
| TypeDefinition | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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
| `le` | Real, defined |
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

7559 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 1997 | 26.4% |
| EqualityElimination | 1610 | 21.3% |
| Reflexivity | 857 | 11.3% |
| Transitivity | 816 | 10.8% |
| Instantiation | 762 | 10.1% |
| BetaStep | 518 | 6.9% |
| Antisymmetry | 395 | 5.2% |
| TypeInstantiation | 309 | 4.1% |
| Assumption | 145 | 1.9% |
| Abstraction | 129 | 1.7% |
| Axiom | 11 | 0.1% |
| Definition | 10 | 0.1% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.
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
!x:num -> num. !y:num. ?z:num. ?u:num. !v:num. NUM_LT v y ==> NUM_BETA z u v = x v
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

50509 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 14819 | 29.3% |
| EqualityElimination | 10987 | 21.8% |
| Reflexivity | 4589 | 9.1% |
| Instantiation | 4550 | 9.0% |
| Antisymmetry | 4114 | 8.1% |
| Transitivity | 3689 | 7.3% |
| BetaStep | 3096 | 6.1% |
| TypeInstantiation | 1831 | 3.6% |
| Assumption | 1551 | 3.1% |
| Abstraction | 1252 | 2.5% |
| Definition | 27 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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

53902 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 17609 | 32.7% |
| EqualityElimination | 11023 | 20.5% |
| Reflexivity | 4986 | 9.3% |
| Instantiation | 4563 | 8.5% |
| Antisymmetry | 4024 | 7.5% |
| Transitivity | 3822 | 7.1% |
| BetaStep | 3204 | 5.9% |
| TypeInstantiation | 1820 | 3.4% |
| Assumption | 1445 | 2.7% |
| Abstraction | 1371 | 2.5% |
| Definition | 31 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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

58839 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 16695 | 28.4% |
| EqualityElimination | 13094 | 22.3% |
| Reflexivity | 5471 | 9.3% |
| Instantiation | 5330 | 9.1% |
| Antisymmetry | 4860 | 8.3% |
| Transitivity | 4291 | 7.3% |
| BetaStep | 3693 | 6.3% |
| TypeInstantiation | 2201 | 3.7% |
| Assumption | 1811 | 3.1% |
| Abstraction | 1358 | 2.3% |
| Definition | 31 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

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

69129 inferences. The account above describes them and is not a second proof: what the kernel checked is this, and its shape is

| rule | inferences | share |
|---|---|---|
| Congruence | 20079 | 29.0% |
| EqualityElimination | 15194 | 22.0% |
| Reflexivity | 6266 | 9.1% |
| Instantiation | 6155 | 8.9% |
| Antisymmetry | 5753 | 8.3% |
| Transitivity | 4916 | 7.1% |
| BetaStep | 4243 | 6.1% |
| TypeInstantiation | 2509 | 3.6% |
| Assumption | 2175 | 3.1% |
| Abstraction | 1799 | 2.6% |
| Definition | 36 | 0.1% |
| TypeDefinition | 2 | 0.0% |
| Axiom | 2 | 0.0% |

## What on this page is checked

- The statement, in both forms, is rendered from the theorem. The second form was read back
  and gave the same term, which is what `Signature.readable` returns a pair for.
- What it rests on is a walk over the derivation, and a name appears against a fact only
  where the sequents agree.
- The inferences and their shape are counted from the same walk.

Not checked, and not claimed: that the statement says what somebody meant, which is what the
readable form is printed for; that a constant is spelled the way the literature spells it,
which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
worth proving.

<!-- end generated: examples -->
