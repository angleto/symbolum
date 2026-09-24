# Notation and prerequisites

**EXCERPT — for anyone scanning the index:**
What every symbol in this repository's documents means, what you are assumed to know before reading
them, and where to look up what is not explained here. Written for somebody at the level of a
mathematics undergraduate: if a term or a symbol appears in any document without a definition or a
precise reference, that is a defect in this page rather than something the reader should have known.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## What you are assumed to know, and what you are not

**Assumed:** what a proof is, what an axiom is, what it means for a statement to follow from
others, and ordinary first-year notation for sets and functions. Nothing else.

**Not assumed, and explained either here or at the reference given:** higher-order logic, simple
type theory, what a definitional extension is, what a type definition is, what a trusted base is,
and what it means for a proof to be checked by a kernel. If you have met first-order logic and not
higher-order logic, the one sentence that matters is in [the section on it](#why-the-logic-is-higher-order).

## The turnstile, which nothing else defines

`|-` is the **turnstile**, and `H1, ..., Hn |- C` is a **sequent**: from the hypotheses on the left,
the conclusion on the right follows. It is read "proves" or "entails".

    |- !x:real. x + 0 = x          nothing is assumed; this is a theorem outright
    p |- p \/ q                    under the assumption p, the disjunction follows
    p, q |- p /\ q                 under two assumptions

**The left side is the whole of what a theorem costs you at that moment**, and this repository is
built around making it visible: a `Kernel.Thm` carries its hypotheses, and a derivation that has
quietly left one standing is a derivation that proved something weaker than it looks. Most specs
here assert `hypotheses shouldBe empty` for exactly that reason.

`|-` is used throughout `proving.md` and in `README.md`, and until this page existed neither said
what it was.

## The symbols

Meanings here; **precedence and associativity are not repeated here on purpose**. They are one row
per spelling in the generated table in
[reading-register.md](reading-register.md#the-notation-27), which is written from
`Notation.standard` by a command and checked by a test. A second copy in this file would be the
exact defect this repository has recorded five times: a figure maintained by hand beside the one the
code knows.

### Connectives

| Written | Means | Note |
|---|---|---|
| `~ p` | not `p` | defined as `p ==> F`, so it costs no axiom |
| `p /\ q` | `p` and `q` | right-associative: `a /\ b /\ c` is `a /\ (b /\ c)` |
| `p \/ q` | `p` or `q`, inclusive | right-associative |
| `p ==> q` | if `p` then `q` | right-associative, so `a ==> b ==> c` is `a ==> (b ==> c)` |
| `p <=> q` | `p` if and only if `q` | the **same constant** as `=`, fixed at `bool -> bool -> bool` |
| `F` | falsity | |

**Every one of these is a definitional extension**, which is the point of the column: they are
defined from equality and universal quantification and add nothing to what you are asked to believe.
`docs/adr/0009` records the three that are not.

### Equality, and the arithmetic the parser also reads

| Written | Means | Note |
|---|---|---|
| `x = y` | `x` equals `y` | the one primitive relation; `<=>` is this constant at `bool` |
| `x + y` | sum | `real` **or** `num`, and the elaborator decides which |
| `x - y` | difference | over `num` this is **truncated**: `3 - 5` is `0`, not `-2` |
| `x * y` | product | `real` or `num` |
| `x / y` | quotient | the reals' division; `num` has no `/` in the notation |
| `- x` | negation | prefix, the reals only |
| `x < y`, `x <= y` | strictly less, at most | `real` or `num` |
| `x > y`, `x >= y` | the same two read backwards | **read only**: the parser accepts them, the printer never writes them |

**One symbol, more than one constant.** `+`, `*`, `<` and `<=` each stand for a real operation and a
`num` one, and which is meant is decided by what the surrounding term forces rather than by the
parser. `docs/adr/0018` is the decision and says why `-` and `/` are **not** overloaded: truncated
subtraction and floor division are not the same operations as the field's, and a reader who wrote
`x - y` expecting the field's would write a false lemma. Those two keep a prefix spelling over `num`,
`NUM_SUB` and `NUM_DIV`.

### Quantifiers and abstraction

| Written | Means |
|---|---|
| `!x. p` | for every `x`, `p` |
| `?x. p` | for some `x`, `p` |
| `\x. e` | the function taking `x` to `e` (a lambda) |

All three **extend as far right as they can**, so `!x. p /\ q` is `!x. (p /\ q)` and not
`(!x. p) /\ q`. This is the single most common way to misread a statement in this repository, and it
is why `Word.RepresentationBody` carries a comment about the parentheses around a negated guard: `~`
takes the widest argument the notation allows, so `~(a) ==> b` and `~(a ==> b)` are different
predicates and only one of them is what anybody meant.

### Types

| Written | Means |
|---|---|
| `x:real` | `x` has type `real` |
| `'a` | a **type variable**: the statement holds at every type |
| `A -> B` | the type of functions from `A` to `B`, right-associative |
| `bool` | the type of propositions |
| `num` | the natural numbers, a **defined** type, not a primitive one |
| `real` | the reals, today **axiomatised**; `docs/adr/0007` decides they will be constructed |
| `word('a)` | a finite word over `'a`; `prod(A, B)` a pair |

A type annotation is written inside the term, and `2:num` against `2:real` is how a numeral whose
type the context does not fix is disambiguated. `docs/adr/0012` is why a numeral nothing determines
is **refused** rather than guessed, and `docs/adr/0018` is why one symbol such as `+` can stand for
more than one constant.

### Application

`f x` is `f` applied to `x`, and it binds tighter than every operator. `f x y` is `(f x) y`:
functions take one argument and return a function, which is why `NUM_ADD x y` and `x + y` are the
same term written two ways.

## Two questions that look like one, and are not

This distinction has been got wrong inside this repository, by two sessions within one hour, and a
reader will meet both numbers on the same page:

- **What a theory asks you to believe** is `Theory.axioms`. It is a property of the development you
  build on, and it is what the table on the front page reports.
- **What a particular proof spent** is `Derivation.axiomsOf`. It is a property of one theorem, and
  it is almost always smaller.

Neither figure is wrong when they disagree; they answer different questions about different
populations, and no check on a single number catches the substitution. The reals as a development
ask for sixteen; a given theorem about the reals may spend three of them and no more.

## Why the logic is higher-order

In first-order logic you may quantify over elements but not over predicates or functions. Here you
may: `!P:num->bool. P ZERO /\ (!n. P n ==> P (SUC n)) ==> !n. P n` is induction as a **single
statement**, quantified over the predicate, rather than a scheme with one instance per formula.
That is what lets induction be a theorem here rather than an axiom scheme, and `docs/adr/0001`
records the decision and what it costs.

The price is that full higher-order unification is undecidable, so the matcher works on a decidable
fragment; `README.md` says which.

## Where to look up what this repository does not explain

Each entry names the specific result rather than the work, because "see Harrison" is not a
reference a reader can act on.

| For | Read | Specifically |
|---|---|---|
| Simple type theory, the logic this is built on | Church, *A Formulation of the Simple Theory of Types*, JSL 5(2), 1940 | the type system and the axioms of the original formulation |
| Why a small kernel makes a large system trustworthy | Gordon and Melham, *Introduction to HOL*, 1993 | the LCF architecture: a private constructor for theorems, and every rule a function returning one |
| The design this one most resembles | Harrison, *HOL Light: An Overview*, TPHOLs 2009 | the ten primitive rules and the definitional extensions built on them |
| Definitional extension, and why it costs nothing | Gordon and Melham, as above | the conservativity of constant definition |
| Defining a type by a bijection with a subset | Harrison, as above, and `docs/adr/0006` here | the type-definition rule and its non-emptiness obligation |
| Gödel's theorems, which this repository is working towards | Gödel, *Über formal unentscheidbare Sätze*, 1931; Boolos, *The Logic of Provability*, 1993 | the arithmetisation of syntax, and the three derivability conditions |
| The beta function, used here to code a finite sequence | Gödel 1931, as above | the remainder trick that makes decoding a single division |
| Match-boundedness, used by a consumer of this system | Geser, Hofbauer and Waldmann, *Match-bounded string rewriting*, NASA/CR-2003-212685 | §6, RFC-match-boundedness |

## What this page does not cover

**Precedence and associativity**, deliberately: [reading-register.md](reading-register.md) has the
generated table, and it is generated because a hand-maintained copy drifts.

**The tactics and what each decides**, which is [proving.md](proving.md).

**The module graph and why it is the correctness argument**, which is
[architecture.md](architecture.md).

**Anything about the algebra half**, which is unchecked by the kernel by design; the front page says
why the two halves are separate and `docs/adr/0003` records it.
