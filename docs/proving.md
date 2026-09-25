# Proving things with Symbolum

**EXCERPT — for anyone scanning the index:**
How to state a proposition, how to get a theorem, and exactly which goals each tactic decides. It
covers the theory of the real numbers as it stands, a map of every development the standard chain
holds and what each one puts in the signature, the three tactics, the derived rules for
proofs written by hand, the bridge to the algebra half, how to look for the assignment that
refutes a claim or shows a set of hypotheses satisfiable, what would have to be assumed for a claim
that does not follow, how a conclusion is traced back to the measurements it rests on, what one
claim costs when all of those are asked at once, what a refusal says to try next, and the text a
person is shown a formalisation in. It does not explain the kernel's
design, which is in [architecture.md](architecture.md), and it does not teach logic.

**What guards the examples below, said exactly, because the sentence that stood here said more.**
`DocumentationSpec` runs a Scala program written beside each assertion and checks the answer against
what the document prints, so an example whose answer stopped being that answer fails the build. What
it does not check is that the text printed here is the program it ran: the two are written twice and
can drift, which is what happened on the front page, where a block nobody could compile sat beside a
green assertion for as long as both existed. `ReadmeSpec` closes that for `README.md` and
`GuideBlocksSpec` closes it for this file, by **compiling** every block as the file holds it.
Compiled is the word that matters, and the measurement that says so is what this guard found here on
2026-09-16, when the file held forty-seven of them: **seven of the blocks below did not compile as printed.** Four carried an
invalid escape, `/\` where a Scala string wants `/\\`, which a lexer rejects before anything is
typed; four failed later, three of them calls that lex perfectly and die in the typer and one a name
the text used and the document never defined. One block is in both counts. A scan that asked only
whether a block lexes would have reported the other three green, and those are the ones that read
like working code. The two guards are a pair: this one says the text is a program,
`DocumentationSpec` says the program gives the answer printed beside it.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## The shape of the thing

A theorem is a value of type `Kernel.Thm`, a final class whose constructor is visible inside
`object Kernel` alone, so the ways to obtain one are the kernel's ten inference rules and its three
theory extensions and there is no other: a value of that type exists because it was derived or
because a theory was extended in one of three declared ways. Everything in this guide is a way of
obtaining one.

**It was an opaque type over a pair until 2026-09-10, and that was not enough.** An opaque type
erases to what it wraps, so `(Nil, p).asInstanceOf[Kernel.Thm]` compiled, ran, and produced `|- p`
out of a tuple, while the assertion that the same pair cannot be *assigned* to that type passed the
whole time: one is about typechecking and the other about erasure. A class does not erase, and
`TrustBoundaryTwinSpec` asserts both halves, the assignment that must not compile and the cast that
must now raise `ClassCastException`. What is enforced by the runtime rather than by the compiler alone is the
difference between a wall and a convention, and it costs one object per theorem.

Every operation that can fail returns `Either[LogicError, Kernel.Thm]` rather than throwing.
Failure is the normal case: a tactic is asked about goals it does not decide, and saying so is its
job.

**`.toOption.get` appears in the examples below and is not how to write this.** It is what an
example does to keep one line to the point when the failure is not what the line is about, and it
throws where a real caller would have to decide something. Anything that matters is written as a
`for` comprehension over the `Either`, which is what the derivations further down do and what the
refusal is for: the first step that fails stops the chain and hands back what it said.

**A refusal says which of three things happened, and it says it in the type.** `LogicError.standing`
is `Decided`, `Exhausted` or `Unread`: the procedure searched to the end of its fragment and the
goal is not in it, or a bound stopped it before it had looked at everything, or it never read the
goal at all. Only the first is an answer, and `LogicError.decided` is the predicate a negative check
is meant to be written with; `TacticError.standing` carries it up to the surface a session drives.

The three were one `Left` with three different sentences inside it until 2026-09-12, and a consumer
reading `Linarith` through a `Try` published an exhausted search as a refutation. What makes that
unrepeatable is not care: `.toOption`, a `Try`, a `catch` and `isLeft` all collapse to *not proved*,
which is the honest weak reading, and the decision is reachable only by naming it. **Decided is not
refuted.** It is decided over the fragment that procedure decides, with what the fragment cannot read
standing in as an unknown, and `DoesNotFollow` says so of itself. What refutes a claim is
`Refutation`, which keeps seven answers apart.

```scala
import garden.xeno.symbolum.theories._

val theorem = Ring.standard.prove("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1")
// Right(|- !x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1)
```

## Stating a proposition

Propositions are written as text and read by a parser that infers types.

```
!x:real y:real. x < y ==> x + 1 < y + 1
```

| Notation | Means |
|---|---|
| `!x:ty. p` | for all `x` of type `ty` |
| `?x:ty. p` | there exists |
| `\x:ty. e` | lambda abstraction |
| `p ==> q` | implication, right associative, binds loosest |
| `p \/ q`, `p /\ q` | disjunction, conjunction |
| `p <=> q` | equality of propositions; `=` is the same constant at any type |
| `~p` | negation, binding looser than `=` so that `~x = y` is `~(x = y)` |
| `x + y`, `x * y`, `x - y`, `-x`, `x < y`, `x <= y` | the arithmetic, declared by the theory rather than built into the parser |
| `x > y`, `x >= y` | the same two relations read from the other end: `x > y` is the term `y < x` |
| `2`, `12`, `1000` | numerals, in binary underneath: `12` is `BIT0 (BIT0 (BIT1 1))` |
| `x:'a` | a type annotation; `'a` is a type variable |

A type the parser cannot determine is an error rather than a guess. `x = y` with nothing to say
what `x` is could be an equation at any type, and a parser that quietly picked one would turn an
unreadable statement into a plausible-looking one:

```scala
Parser.proposition(Logic.standard.theory, "x = y")
// Left(the type of this term is not determined; annotate it. Undetermined: 1 type)
```

Notation belongs to a theory, not to the parser. `Real.notation` adds the arithmetic to the
logical connectives, and a theory of your own would add its own operators with their precedences.

**`>` and `>=` are read and never printed.** `Notation.withFlippedInfix` declares an operator whose
operands the parser swaps as it reads them, `Real.notation` declares both mirror spellings at the
precedence the plain ones have, and what comes out is the same term the plain spelling builds, to
the node, rather than one provably equivalent to it. So the theory gains no constant and no axiom
here: there is one order relation, and every lemma about `<` already covers both ways of writing
it. Nothing prints that way, because `Notation.infixOf` filters the flipped entries out and `Show`
is its only caller, which leaves the printed form the one form that reads back to the term it came
from. `MirrorSpellingSpec` pins all of that, the term identity first.

## The theory

Sixteen axioms, in [`Real.scala`](../modules/theories/src/main/scala/garden/xeno/symbolum/theories/Real.scala),
stating a complete ordered field, and a test asserts the theory holds exactly those and in that
order. They are the whole non-definitional content of the *theory*; since 2026-09-10 there are two
more about the *logic*, a choice operator and eta in `Classical.scala`, which a development takes
only by asking for them. `docs/adr/0007` is the record of the first and `docs/adr/0009` of the
second, and the subsection below is what the pair of them buys and what it did not have to.

```
ADD_SYM         !x y. x + y = y + x
ADD_ASSOC       !x y z. (x + y) + z = x + (y + z)
ADD_ZERO        !x. x + 0 = x
ADD_INVERSE     !x. x + -x = 0
MUL_SYM         !x y. x * y = y * x
MUL_ASSOC       !x y z. (x * y) * z = x * (y * z)
MUL_ONE         !x. x * 1 = x
MUL_INVERSE     !x. ~(x = 0) ==> x * inv x = 1
DISTRIBUTE      !x y z. x * (y + z) = x * y + x * z
ONE_NOT_ZERO    ~(1 = 0)
LT_IRREFLEXIVE  !x. ~(x < x)
LT_TRANSITIVE   !x y z. x < y /\ y < z ==> x < z
LT_TOTAL        !x y. x < y \/ x = y \/ y < x
LT_ADD          !x y z. x < y ==> x + z < y + z
LT_MUL          !x y. 0 < x /\ 0 < y ==> 0 < x * y
COMPLETENESS    !P. (?x. P x) /\ (?b. !x. P x ==> x <= b) ==>
                    (?s. (!x. P x ==> x <= s) /\ (!b. (!x. P x ==> x <= b) ==> s <= b))
```

Subtraction, division, the non-strict order and the two numeral bits are **definitions**, so they
add nothing to what has to be believed. Everything else in the system is proved.

### The excluded middle is derived, and it cost no axiom of its own

`p \/ ~p` is `EXCLUDED_MIDDLE` on `Classical.standard`, and it is a theorem: 841 inference steps by
`Derivation.size`, resting on `SELECT` and on nothing else. That figure is spelled from the
measurement by `DocumentationSpec` rather than written beside it. `ClassicalSpec` asserts that axiom set
rather than describing it, which is what makes the claim a measurement.

**The plan for this change expected it to cost extensionality, and it did not.** Diaconescu's
argument derives the excluded middle from choice together with extensionality, and that is a true
statement about the argument and a false one about this kernel. The argument compares two predicates
over `bool`,

```
U = \x. x = T \/ p        V = \x. x = F \/ p
```

and needs `U = V` from the fact that each holds of everything when `p` does. Both are **literal
abstractions**, and `Kernel.abs` takes `s = t` to `(\x. s) = (\x. t)`: that is function
extensionality already, restricted to functions written as lambdas, and it has been one of the ten
rules from the beginning. What eta adds is the rest of the range, a function arriving as a variable
or a constant, by letting any `f` be read as `\x. f x`. Diaconescu never needs that. Propositional
extensionality, the other half people count, is `Kernel.deductAntisym` and has also been in the
trusted base from the start: two propositions each derivable from the other are equal, which is what
makes `bool` a type of truth values rather than of proofs.

So the derivation reaches for `SELECT`, the kernel's abstraction rule, its deduction theorem and two
disjunction eliminations, and it needs no decision about whether the two chosen values are equal,
which is the step the argument is usually presented as needing. `~(T = F)` is where its
contradiction comes from, and that is 122 steps and no axiom at all.

What comes with it, each derived and each measured. The table below is **generated** by
`sbt "theories/runMain garden.xeno.symbolum.theories.Guide"` and pinned by `GuideSpec`, which is why it says
`!p:bool` where the prose says `p`: the statement column is the text `Classical.Statements` holds
and `ClassicalSpec` checks each derivation against, and the step counts are `Derivation.size` read
off the derivations themselves. A change that moves them fails the suite naming that command.

<!-- generated: classical, do not edit below this line -->

| Theorem | Statement | Rests on | Steps |
|---|---|---|---|
| `TRUTH_NOT_FALSITY` | `⊢ ~(T = F)` | nothing | 122 |
| `DE_MORGAN_DISJUNCTION` | `⊢ !p:bool. !q:bool. (~(p \/ q)) = (~p /\ ~q)` | nothing | 495 |
| `FUNCTION_EXTENSIONALITY` | `⊢ !f:'a->'b. !g:'a->'b. (!x:'a. f x = g x) ==> f = g` | `ETA` | 197 |
| `EXCLUDED_MIDDLE` | `⊢ !p:bool. p \/ ~p` | `SELECT` | 841 |
| `DOUBLE_NEGATION` | `⊢ !p:bool. ~~p ==> p` | `SELECT` | 952 |
| `DE_MORGAN_CONJUNCTION` | `⊢ !p:bool. !q:bool. (~(p /\ q)) = (~p \/ ~q)` | `SELECT` | 1101 |
| `NOT_FORALL` | `⊢ !P:'a->bool. ~(!x:'a. P x) ==> ?x:'a. ~(P x)` | `SELECT` | 1155 |
| `COND_TRUE` | `⊢ !p:bool. !a:'a. !b:'a. p ==> COND p a b = a` | `SELECT` | 482 |
| `COND_FALSE` | `⊢ !p:bool. !a:'a. !b:'a. ~p ==> COND p a b = b` | `SELECT` | 482 |

<!-- end generated: classical -->

The last two rows are the conditional, and they are the reason the table has nine. `COND p a b` is
**defined**, not assumed: `select` names the thing satisfying `(p ==> x = a) /\ (~p ==> x = b)`, and
something satisfies that whichever way `p` falls, which is the content of the two equations. So the
chain gained a conditional on 2026-09-12 and the count of nineteen did not move, which `ChainSpec`
asserts. Before that date there was no conditional constant anywhere in it, and a function defined
by cases had nothing at all to write its cases with.

They rest on `SELECT` and never reach `EXCLUDED_MIDDLE`, which is worth a line. The obvious proof of
each is a case split on `p`, and that would put the whole of the excluded middle's derivation
inside both, at the cost the table above gives; instead
the value is offered to the choice axiom directly and the conjunct that matches the case is read off
the answer.

`COND` has no spelling of its own: it is written `COND p a b`, at application precedence, because
this notation offers infix, prefix, binder and numerals and every one of them is fixed at one or two
arguments. `if p then a else b` is a mixfix with two keywords and is a change to the parser and the
printer rather than a row in the precedence table. `Classical.scala` carries that decision and what
it does not cover.

The two resting on nothing are collected here rather than bought here, and they are in the table for
that reason: a reader asking what the classical extension costs should be able to see which of what
it offers was always available. De Morgan is the pair that shows the difference plainly. From
`~(p \/ q)` both negations follow directly and no axiom is touched; from `~(p /\ q)` nothing
intuitionistic says which of the two fails, and the derivation is two nested case splits.

Neither axiom appears in the other's derivations, which `ClassicalSpec` also asserts. They are
independent purchases, and a development could take either alone.

`~` takes the widest argument this notation allows, which is why a negated side of an equation is
parenthesised above. `~(p \/ q) = (~p /\ ~q)` reads as `~((p \/ q) = (~p /\ ~q))`, a different and
false statement, and writing the De Morgan entries without the parentheses is how that was found.

## What the chain holds, development by development

The sixteen axioms above are what the *reals* are, and most of what this system can state is not
about them. The naturals, the pair, the word, the matrix, number theory on `num`, the arithmetisation
of this system's own syntax and the first analysis are developments stacked into one chain, and that
is what lets a claim name a constant of any of them: they share one signature rather than each
having one of its own. `Chain.standard` assembles the stack, `Chain.widest` is the signature it ends
at, and that signature is what `Ask`, `Find` and the notebook read a claim against.

This table is the map, and the question it answers is which name to look under. It says what each
development puts into the signature and what it is for; it does not list the lemmas, which are in
[lemmas.md](lemmas.md) under the heading this table's first column names. `DocumentationSpec`
compares the two in both directions and fails when the chain holds a development this table does not
name, or when this table names one the chain does not hold, so a link added to `Chain.construct`
lands red here rather than going unmentioned.

| Development | What it puts in the signature | What it is for |
|---|---|---|
| `Classical` | `COND` | A case split about a proposition, and a function defined by cases. It holds the excluded middle, both De Morgans, double negation, function extensionality and `NOT_FORALL`, every one of them derived; what it costs is the two axioms of the logic, `SELECT` and `ETA` |
| `Real` | `+`, `*`, `-`, `/`, `inv`, `<`, `<=`, `0`, `1` and the two numeral bits | The complete ordered field of the sixteen axioms above. Subtraction, division, the non-strict order and the bits are definitions, which is why what a reader is asked to believe is sixteen and not twenty-one |
| `Positivity` | nothing | Three facts about `0 <` that `Order` re-exports. The listing shows both holders rather than one, because a lookup returning the first would be picking by map iteration order |
| `Order` | nothing | The order worked out: antisymmetry, the case split, cancellation on both sides, `SQUARE_NONNEG`, and the two lemmas that turn a negated comparison into the other one without costing anything classical |
| `Natural` | the type `num`, `ZERO`, `SUC`, and the type `ind` with `IND_0` and `IND_SUC` under it | The naturals as a **defined** type, carved out of an infinite one as the smallest inductive subset. Induction, Peano's other axioms and the recursion theorem are all derived here rather than assumed; what is assumed is `INFINITY`, and that is the whole of what the type costs |
| `Peano` | `NUM_ADD`, `NUM_MUL`, `NUM_LE`, `NUM_LT`, `PRE`, `NUM_SUB`, `real_of_num` | The arithmetic and the two orders on `num`, the embedding into the reals, the truncated subtraction that is the only one `num` can have, strong induction, the least and the greatest number principles, and `NUM_ARCHIMEDES`, which is the first of the two places `COMPLETENESS` is spent |
| `Series` | `Sum`, `Prod`, `Power` | Finite sums, products and powers, built on the recursion theorem: linearity, the telescoping sum, summation by parts, reindexing, the geometric sum and the exchange of two summations |
| `Divisibility` | `Divides` | Divisibility over the **reals**, which is the weaker of the two here: over a field the antisymmetry is false, and the version of it that holds is `Modular`'s |
| `Modular` | `NUM_DIVIDES`, `NUM_CONG`, `NUM_GCD`, `NUM_DIV`, `NUM_MOD`, `NUM_PRIME` | Number theory on `num`: congruences with their compatibility with the operations, division with remainder in both halves, the greatest common divisor, Bezout, Euclid's lemma and the definition of a prime. `NUM_GCD` is **chosen** rather than computed, since Euclid's algorithm is a definition by well-founded recursion and this system has no such rule |
| `Product` | the type `prod`, `PAIR`, `FST`, `SND` | The pair, carved out of `'a -> 'b -> bool` the way `pair.ml` does it. It is the one primitive that lists, matrices and index types were all waiting on |
| `Word` | the type `word`, `WORD_LENGTH`, `WORD_NTH`, `WORD_MAKE`, `WORD_PAD` | A finite word: a length and a padded function held together in a pair, with the extensionality that says two words agreeing at every index are the same word |
| `Matrix` | `MAT2`, `MAT_ADD`, `MAT_SMUL`, `MAT_MUL`, `MAT_ID`, `MAT_TRANSPOSE`, `MAT_DET` | Two-by-two real matrices, as far as the determinant being multiplicative |
| `Rotation` | `WORD_ROTATE` | Rotating a word. It is a development of its own rather than part of `Word` because it needs two things at once: `Word` for the type it rebuilds, and `Modular` for the `NUM_MOD` inside its own definition |
| `Magnitude` | `max`, `min`, `abs`, `sgn` | The four, with the triangle inequality among them. `ABS_TRIANGLE` is the one theorem here whose derivation is recorded step by step, and [theorems.md](theorems.md) prints it |
| `Coding` | `NUM_FACT`, `NUM_PROD`, `NUM_BETA` | The arithmetic that coding syntax as numbers needs: the factorial, the product of a family, Gauss's lemma, the Chinese remainder theorem over `n` moduli rather than two, and the beta function, which is what makes any finite stretch of a sequence two numbers |
| `Primes` | nothing | The facts about the primes that are results rather than infrastructure: that there is no largest one; that no square is twice a square at a positive denominator, which is the arithmetic content of the irrationality of the square root of two and is deliberately not that sentence; and the fundamental theorem of arithmetic, whose uniqueness half is an equation between two **non-decreasing** families rather than a claim about a multiset, since there is no multiset here to make one with |
| `Numbering` | `NUM_TRI`, `NUM_PAIR`, `NUM_CODE`, and the four projections that take one apart | Cantor's pairing written on the triangular numbers so that no division appears, and a constructor that codes a tag and a payload as one number. What the whole construction exists for is that both components of a pair are at most the pair |
| `Language` | `NUM_TERM`, `NUM_FORM`, `NUM_NUMERAL`, `NUM_SUBST_TERM`, `NUM_SUBST_FORM`, `NUM_FREE_TERM`, `NUM_FREE_FORM`, `NUM_CLOSED`, `NUM_PA`, `NUM_LOGIC`, and six abbreviations | The language of Peano arithmetic, as predicates on `num` and not as a datatype: being a term, being a formula, substituting for a free variable, where a variable occurs free, the axioms of PA and the eight schemes of first-order logic with equality |
| `Provability` | `NUM_STEP`, `NUM_PROOF`, `NUM_PROV`, `NUM_STEP_FROM`, `NUM_PROV_FROM` | What the embedded theory can prove, as a formula with its subject free. Not one of its definitions is a recursion, and that is the whole return on coding a sequence with the beta function rather than by iterating a pairing |
| `Deduction` | nothing | Derivations **of** the embedded theory: five schemes proved for every formula rather than at one code, and the deduction theorem over them. It is the first link that declares nothing, which is the day the last link and the widest signature stopped being the same thing |
| `Truth` | `NUM_VALUE`, `NUM_TRUE`, `NUM_TRI_GRAPH` | What a term of the embedded theory is worth and whether a formula of it holds, at an environment giving each variable a number, and the triangle's graph as the first formula whose truth is a predicate of this logic. `docs/adr/0040` is why a representation is stated this way; nothing in it says what PA proves |
| `Limit` | `converges`, `lim` | The first analysis here: the epsilon-N statement written out, the limit named by choice and pinned wherever the sequence converges, the monotone convergence theorem, which is the second place `COMPLETENESS` is spent and the first thing here that **obtains** a limit rather than assuming one, and the comparison test over it |
| `Transcendental` | `exp`, `sin`, `cos`, `ln`, `sinh`, `cosh` | The transcendental functions as their power series through that limit rather than as four characterising axioms, which is what `docs/adr/0017` decides and what it rejects. What is proved of them here is the value of each at zero, `2 < exp 1`, the exponential's absolute convergence and addition theorem, the hyperbolic identity, and `sin x * sin x + cos x * cos x = 1` through a second pair of Cauchy products; the facts about `ln` are `Logarithm`'s |
| `Concatenation` | `WORD_EMPTY`, `WORD_SINGLETON`, `WORD_CONCAT`, `WORD_PREFIX`, `WORD_SUFFIX`, `WORD_FACTOR` | Putting two words together, with the prefix, the suffix and the factor each defined **by** the concatenation rather than beside it. Before it, `?x y. w = WORD_CONCAT (WORD_CONCAT x u) y` was not a sentence this system could write, so of a factor nothing could be said, not even wrongly |
| `Inductive` | `MONOTONE`, `INDUCTIVE` | The set given by a rule set, as the intersection of every closed set rather than as an iteration. What that buys is a **non**-membership: a closure that can only be generated forwards answers a membership for whatever the budget reached and answers nothing at all about what is outside it |
| `Reaching` | `REACH` | What a rewriting relation reaches, and the first consumer of `INDUCTIVE`: an induction principle over the reachable pairs, and a potential-function argument that bounds how many counted steps a derivation can hold |
| `Forward` | `WORD_STEP`, `WORD_RFC` | The right forward closure of a string rewriting system, which is the technique a quadratic lower bound on derivation length is read off (Geser, Hofbauer and Waldmann, NASA/CR-2003-212685). `WORD_STEP` is one rule applied anywhere inside a word; `WORD_RFC` is the least set holding the right-hand sides and closed under that and under extending a member on the right by a rule overlapping its end. The second consumer of `INDUCTIVE`, and the one that needed `WORD_CONCAT`: the inside-reduction clause says the left side occurs with a context on each side, and both sides of one step need the **same** context |
| `Integer` | `INT_SAME`, `INT_OF_PAIR`, `INT_OF_NUM`, `INT_ADD`, `INT_NEG`, `INT_MUL`, `INT_ZERO`, `INT_ONE`, `INT_DIVIDES`, `INT_LE` | The integers, as the classes of `prod(num,num)` under `FST p + SND q = FST q + SND p`, which is `a - b = c - d` written so that no subtraction appears: `num`'s is truncated, so the reading with a `NUM_SUB` in it is not an equivalence. The first real consumer of the quotient builder, and `docs/adr/0033` is why it arrives as a prerequisite of two blocked formalisations rather than as step 4 of the construction of the reals. An ordered ring with a divisibility over it, at **no axiom** beyond the carrier's choice, eta and infinity and none of the sixteen. What it is for is that `Divides` is over the reals, where every non-zero element divides everything, so the condition is discharged vacuously, and `NUM_DIVIDES` cannot state it at all over signed coefficients. The operations keep a prefix spelling for `docs/adr/0018`'s reason read at a third type |
| `Inclusion` | `real_of_int` | The integers inside the reals, and the one piece of `Integer` that mentions a real: the embedding is a ring homomorphism, it agrees with `real_of_num` through `INT_OF_NUM`, and it is injective. It is a link of its own rather than a section of that file because `Integer.scala` says of itself that nothing in it reaches for a real and `docs/adr/0033` rests phase 5's move of that development on the sentence. It is also where the axiom accounting divides: every fact here reaches the sixteen, because every fact here is an equation between reals and `Ring` decides those out of the field, and no fact of `Integer` reaches any of them |
| `Listing` | `LIST_CONS`, `LIST_HEAD`, `LIST_TAIL` | The list interface over `word`, which is an orientation and not a carrier: `docs/adr/0038` measures that `word('a)` is already a type operator of arity one, already has `WORD_EMPTY`, `WORD_SINGLETON` and `WORD_CONCAT`, and that a second carve would be from the **same** predicate and inherit none of its facts. What was missing is one principle: `WORD_INDUCTION` extends a word on the right, and a definition by recursion on a sequence descends from the left. So `LIST_CONS x w` is `WORD_CONCAT (WORD_SINGLETON x) w` under a name, the empty list is `WORD_EMPTY` with no second name, and `LIST_INDUCT` is cons-induction. Three definitions, **no axiom and no type**. `LIST_RECURSION` is the principle a *definition* needs, where `LIST_INDUCT` only proves things: it is `Recursion.theorem` at the result type `word('a) -> 'b`, read at the word's own length, and it is why `LIST_HEAD` and `LIST_TAIL` are constants rather than terms built inside a proof. `LIST_RECURSION_UNIQUE` is the other half, since this logic has no unique-existence quantifier |
| `Folding` | `LIST_FOLD` | The consumer of `LIST_RECURSION`, and the first thing here written with lists that `word` writes by index. `LIST_FOLD g a (LIST_CONS x w)` is `g x (LIST_FOLD g a w)`, so `LIST_FOLD_CONCAT` splits over an append with **no index correction** where `WORD_CONCAT_TALLY` carries `NUM_ADD (WORD_LENGTH u) i`. One definition, no axiom, no type. What a fold cannot express is the other half of that sentence: a measure weighing a letter by where it sits, which is what the tally is for and why it is not superseded |
| `Root` | `sqrt` | The square root of a non-negative real, named by choice, and `SQRT_EXISTS`, which says what it names exists: the least upper bound of the numbers whose square is at most `x` squares to `x`, which is `COMPLETENESS` read a third time and the reason the existence rests on the reals alone. `SQRT`, `SQRT_UNIQUE` and `SQRT_SQUARE` read the choice back; nothing is said below zero, where the choice falls somewhere, and `RootSpec` refutes the unconditional statement at minus one |
| `Continuity` | `continuous` | Continuity at a point, the epsilon-delta statement written out, and `INTERMEDIATE_VALUE`: a function continuous on `[a, b]` takes every value between `f a` and `f b` in it, which is `COMPLETENESS` read a fourth time. `CONTINUOUS_CONST` and `CONTINUOUS_ID` are the two functions everything else will be built from; `ContinuitySpec` shows a step is not continuous and refutes the theorem without its continuity hypothesis at that step. Since 2026-09-25 also the extreme value theorem, `CONTINUOUS_ATTAINS_MAX` and `CONTINUOUS_ATTAINS_MIN` with `CONTINUOUS_BOUNDED` under them, and all three are one lemma used twice: `INTERVAL_GLUING`, that a property of intervals which glues end to end and holds on every short interval around each point holds on `[a, b]`. `CONTINUOUS_NEG` is what turns the maximum into the minimum. `CONTINUOUS_LINEAR`, a linear combination of two continuous functions, since 2026-09-25 for the mean value theorem |
| `Logarithm` | nothing | The first facts about `ln`, and what they wait on: the exponential positive, strictly increasing, continuous everywhere from one estimate near zero, and onto the positive reals by the intermediate value theorem; then `EXP_LN`, `LN_EXP`, `LN_ONE` and `LN_MUL`. It declares nothing, as `Deduction` does, because its subject is three constants declared below it |
| `Resolving` | `RES_SAT`, `RES_JUSTIFIED`, `RES_REFUTATION`, `RES_WIDTH` | Resolution as an object: a step sound, a derivation sound by strong induction on the step index, and a derivation reaching the empty clause leaving **no** assignment satisfying the inputs. The refutation, satisfaction and width have names since 2026-09-25, so a statement about every refutation of a family is written without coding one: a refutation is three functions and a step count, its size is that count, and its width is the largest clause, defined by recursion on the count. It is the floor Cook and Reckhow require of a proof system and not a lower bound |
| `Derivative` | `derivative` | The derivative at a point, written with no quotient: `abs (f (x + h) - f x - m * h) < e * abs h` for every non-zero `h` inside the radius, which keeps every step inside what `Linarith` decides. `DERIVATIVE_INTERIOR_MAX` and `DERIVATIVE_INTERIOR_MIN` are Fermat's lemma, the minimum being the maximum at `\y. 0 - f y` through `DERIVATIVE_NEG`, and `ROLLE` is the first thing to spend the extreme value theorem, at exactly its price. `DERIVATIVE_CONST` and `DERIVATIVE_ID` keep the definition from being empty; `DerivativeSpec` shows the identity is flat nowhere and refutes Rolle without `f a = f b` there. `MEAN_VALUE` is Rolle at `(b - a) * f y - (f b - f a) * y`, with `DERIVATIVE_LINEAR`, `DERIVATIVE_UNIQUE` and `Continuity`'s `CONTINUOUS_LINEAR` in front of it. `DERIVATIVE_PRODUCT` is the product rule, with `DERIVATIVE_CONTINUOUS` under it to keep the second factor in hand; `DERIVATIVE_CHAIN` is the chain rule, which holds where `g` is flat without dividing by its increment |

**This is not the front page's table and the two must not be merged.** `README.md` indexes by
**capability**, so a row of it is a thing a reader might want to state and the answer is yes or no
with the development named where there is one; several of its rows are a **No**, which is the half
this table cannot have, since a development that does not exist has nothing to put in a signature.
This one indexes by development and is the map you want once the answer is yes and the question is
where to look. A reader who finds them saying different things about the same development should
believe this one and fix that one: this table is compared against the library by a test and that
table is prose.

**What is not in the table, and why the absence is not an omission.** A development that publishes no
lemma of its own has no heading in `lemmas.md` and no row here. They are drivers and procedures,
and this sentence counted them until 2026-09-25, when a tenth made the count false: `Induct` runs
an induction over a goal, `Bounded` discharges `!i. i < k ==> P i` at a concrete bound by proving
the instances, `Successor` puts a numeral into successor form so that a recurrence can reach it,
`Monotone` hands back `|- MONOTONE f` for an operator written in the usual shape, `Recursion` and
`Quotient` define the **caller's** constant and the caller's type, `Datatype` defines the caller's
inductive type from its constructors and a function on it by structural recursion
(`docs/adr/0042`), `WellFounded` proves recursion along a measure for the caller's step
(`docs/adr/0043`), `Descent` defines a predicate by recursion on a code, and `Domain` builds a
caller's own theory of a domain that is not mathematics. `Resolving` was on this list until the
same day, when it became a link with lemmas of its own and a row above. Nothing they produce
belongs to them, which is why there is nothing of theirs to list.
`Ring`, `Field`, `Linarith`, `Arithmetic` and `Order`'s procedures are the section below.

**The position of a development in the chain is its extension order and not its dependency order**,
and the two are different on purpose. `Inductive` needs nothing from anything below it and sits at
the end anyway, because a constant declared into a side branch is unreachable from everything above
it: `Chain.widest` is built over the **last** extension, so a development that extended the theory it
happened to need would put its constants somewhere no later claim could name them. The comment in
`Rotation.construct` is where that argument is written down.

## Proving: the tactics

### `Ring` — identities of a commutative ring

Puts both sides in a normal form and checks that they became the same term. The normal form is a
sum of monomials in a fixed order, each of them a rational coefficient times a sorted product of the
atoms it could not take apart, so `2 * x` stays `2 * x`, `x + x` becomes `2 * x` as well, and
`x / 2 + x / 2` becomes the coefficient `1` on `x` rather than a monomial with `inv 2` among its
atoms.

```scala
Ring.standard.prove("!x:real y:real. (x - y) * (x + y) = x * x - y * y")
Ring.standard.prove("!x:real y:real. -(x + y) = -x + -y")
Ring.standard.prove("2 * 3 = 6")
```

**Decides:** equations built from `+`, `*`, `-`, `/`, unary `-`, numerals and variables, with a
denominator that is any non-zero constant carried as a rational coefficient, and any other `inv`
allowed as an opaque atom.
**Refuses:** any equation whose truth needs `x * inv x` to become `1` for a symbolic `x`, anything
that is not an equation, and any equation that is not an identity.

**A constant denominator is decided, and it costs no hypothesis.** `x / 2 + x / 2 = x` is proved,
and so is `x / 2 + x / 3 = 5 * x / 6`. The step it needs is `2 * inv 2 = 1`, which is `MUL_INVERSE`
under `~(2 = 0)`, and for a numeral that side condition is a theorem: `Positivity.numeralNonZero`
proves it, so it is discharged rather than carried and what comes back is unconditional. A
coefficient in the normal form is a rational number, written `n * inv d` in lowest terms with the
sign on the numerator, and `Coefficient` is where its arithmetic lives.

**A denominator that is a constant but not a numeral is decided too, since 2026-09-09**, so
`x / (-1) = -x` and `x / (2 / 3) = 3 * x / 2` are proved. `Positivity` says nothing about `-1` or
about `2 / 3`, and it does not have to: `Coefficient.inverseOfUnit` is `!x y. x * y = 1 ==>
inv x = y`, so the reciprocal this file computes anyway is the witness that the denominator is not
zero. The side condition is discharged by the arithmetic rather than by the order, which is what
keeps the order above the ring where it belongs: the other route wants `0 < inv d`.

`inv 0` is not a denominator and stays an atom, which is why `x / 0 + x / 0 = 2 * (x / 0)` is proved
and says nothing about what `x / 0` is.

A quotient is inside the fragment and used not to be. `x / y` abbreviates `x * inv y`, so unfolding
it needs nothing; what needs `~(y = 0)` is cancelling `y` against `inv y`, and `Ring` does not do
that. The two were treated as one thing until 2026-09-08, so no identity with a quotient in it was
decided at all. Cancelling is `Field`, below.

**There are two normal forms, and the other one has not been retired.** `Ring.expanding` is the
tactic over the form this file used to describe: it unfolds the binary numerals, so `2 * x` becomes
`(1 + 1) * x`, then `1 * x + 1 * x`, then `x + x`, and a coefficient of `k` costs `k` copies of the
term. It decides the same fragment. It is kept because it is what proves the structural lemmas the
collecting form runs on, and because a claim about the difference between two procedures is worth
what the pair of measurements behind it is worth.

The size of each form is exact rather than a rule of thumb, and `RingCostSpec` asserts both up the
ladder. Expanding, `k * x` has `4k - 3` nodes and `(x + 1)^k` has `k * 2^(k+1) + 1`: 769 nodes at
degree six and 98305 at degree twelve, which is why degree six was the ceiling and why `12 * 12`
reached 573 nodes with nothing symbolic in it. Collecting, `k * x` has `2 * bits(k) + 3` nodes, so
it follows the length of the coefficient rather than its value, and `(x + 1)^k` has `k + 1`
monomials: 133 nodes at degree six and 507 at degree twelve.

What that bought, measured inside the suite on 2026-09-04 and warm: `12 * 12` in 2 ms against
528 ms, `(x + 1)^12` in 143 ms where the expanding form does not finish, and `1000 * x`, which this
file used to call out of reach, in 2 ms. Read the times as orders of magnitude: the same
measurements taken cold, outside the suite, were four to ten times slower and gave sizes identical
to the node. That is why the assertions are sizes.

The wall that is left is a different one, and it is not in the algebra. A coefficient is added and
multiplied by the numeral procedures in `Arithmetic`, so the cost now follows the arithmetic:
`Oracle.NumeralBudget` is where it is written down, and the comment there carries the measurement
that set it.

### `Field` — identities that need a denominator to be non-zero

The same normal form as `Ring`, plus the one step `Ring` will not take: `x * inv x` becomes `1`. The
axiom that licenses it has an antecedent, so the step costs a hypothesis, and the tactic pays it by
assuming `~(x = 0)` and letting that assumption travel to the caller in the sequent.

```scala
Field.standard.prove("!x:real y:real. (x * y) / y = x")
// Right(~(y = 0) |- !x. x * y / y = x)
```

Read what came back rather than only that something did. Two things about it are the point:

- **The hypothesis is there.** It is not discharged, not folded into an implication, not dropped.
  `Field.conditions(theorem)` is the same list under a name that says why you should look at it.
- **`y` lost its quantifier.** A variable a hypothesis mentions cannot be generalised, and the
  kernel refuses to. So the theorem is about *a* `y` that is not zero, not about every `y`, and the
  sequent says exactly that. This is weaker than the goal as written and it is the strongest true
  statement of that shape.

**Decides:** everything `Ring` decides, plus identities that hold wherever the denominators are
non-zero, whatever those denominators are built out of.
**Refuses:** an equation that is still false with the denominators assumed non-zero.

**A denominator is taken apart before it is assumed about, since 2026-09-09.** `inv (2 * y)` was one
atom and `(2 * x) / (2 * y) = x / y` was refused; it is proved now, assuming `~(y = 0)` and nothing
about the `2`, because a numeral's condition is a theorem. The recursion covers a product, a
negation and an inverse alike, so `inv (24 * x)`, `inv (-x)` and `inv (inv x)` are one mechanism and
only an atom ever costs a hypothesis. That was the last thing standing between this tactic and the
field goals of Mathlib's own ring corpus, and track F of [evaluation.md](evaluation.md) now proves
all three.

The lemma behind it is `Coefficient.inverseOfUnit`, `!x y. x * y = 1 ==> inv x = y`, and what it
avoids is the reason it arrived: the obvious route wants `~(a * b = 0)` from `~(a = 0)` and
`~(b = 0)`, which is the absence of zero divisors. A factor of one cannot be zero, so the reciprocal
the tactic builds anyway is the witness, and no such fact is needed or proved.

**Splitting is the second attempt, not the first.** A rule that fires puts its conditions on the
theorem whether the proof needed them or not, and `(z * x) / (2 * y) = z * (x / (2 * y))` is true at
`y = 0` as well. So a goal is tried without the split first, and only a goal that needed one pays
for it.

**A constant denominator does not reach here at all any more.** `x / 2 + x / 2 = x` was refused by
this tactic until 2026-09-09, and not for the side condition: `~(2 = 0)` is provable, so nothing was
owed. The obstacle was that a numeral is a monomial's coefficient in the normal form and never one
of its atoms, so `2 * (x * inv 2)` kept the two halves of the cancellation on opposite sides of that
split. A coefficient can now be `1 / 2` and its reciprocal is computed rather than assumed about, so
every constant denominator is settled by `Ring` with nothing assumed. What is left for `Field` is a
denominator with a variable in it: a constant one carries its own reciprocal and a factor of one
cannot be zero, and `inv 0`, which nothing multiplies to one, stays the atom it was. A symbolic
denominator has no reciprocal to compute, and it is the kind whose being zero the theory cannot
rule out.

**A condition is assumed only if it was used.** The tactic reads the denominators off the normal
form and prepares a cancellation rule for each, but a rule that never fires contributes no
hypothesis, because a hypothesis reaches a theorem only through the inference that used it. So
`(z * x) / (2 * y) = z * (x / (2 * y))` comes back with nothing assumed: it is true for every `y`,
including zero, and the tactic does not pretend to have needed anything.

**Discharging the condition.** `Order.nonZero` is `!x. 0 < x ==> ~(x = 0)`, so a denominator known
positive settles it and the theorem is left resting on the positivity instead:

```scala
for {
  discharged <- rules.disch(theorem.hypotheses.head, theorem)   // |- ~(y = 0) ==> ...
  result <- rules.mp(discharged, derived)                       // 0 < y |- ...
} yield result
```

**Why the atoms are ordered differently.** A rewrite fires between neighbours, and under
`Arithmetic.ringOrder` the atoms `y` and `inv y` are not neighbours: `inv y` is an application and
sorts with the applications, so any variable between them keeps the cancellation rule from ever
matching. `Field.atomOrder` compares an atom by what is under its inverses first, which is what
`ringOrder` already does for negations and for the same reason. `Polynomial` takes the order as a
parameter so that nothing else moves.

### `Linarith` — linear arithmetic

Moves every inequality to the form `0 < e`, looks for non-negative multipliers that build the
goal's difference out of the hypotheses' differences, and checks the combination with `Ring`.

```scala
Linarith.standard.prove("!x:real y:real z:real. x < y /\\ y < z ==> x < z")
Linarith.standard.prove("!x:real y:real. 2 * x < 2 * y ==> x < y")
Linarith.standard.prove("!x:real. x < x + 1")
Linarith.standard.prove("!x:real y:real. 3 * x < 2 * y /\\ 2 * y < 5 * x ==> 0 < x")
Linarith.standard.prove("!x:real y:real z:real. x <= y /\\ y < z ==> x < z")
Linarith.standard.prove("!a:real b:real. a = 53 * b /\\ 0 < b ==> a <= 60 * b")
```

**Decides:** a goal `h1 /\ ... /\ hn ==> c` where each hypothesis is `a < b`, `a <= b` or `a = b`
and the conclusion is `a < b` or `a <= b`, and it decides that fragment rather than a corner of it.
Such an implication is valid exactly when the conclusion's difference is a non-negative rational
combination of the hypotheses' differences plus a non-negative constant, with an equality free to
be weighed either way, or when the hypotheses cannot all hold at once; both are one linear program,
and `Farkas` solves it.
**Refuses:** anything neither the linear form, the hypotheses multiplied, nor one completed square
reaches. The pairs get to degree two, and a second round crossing those products with the
hypotheses gets to degree three, run only when the goal names an atom the pairs did not reach, so
a product of four unknowns is past what the products make. The square is the one fact in the pool
that is not made from the goal's hypotheses, and it is what a goal with **no** hypotheses has: over
an atom that is one unknown times itself the square is completed, and `SQUARE_NONNEG` at that
argument is the fact, checked by the kernel like the others. `docs/adr/0032` is the decision.

```scala
Linarith.standard.prove("!a:real. a * (2 - a) <= 1")
```

The refusal names the atom and how many unknowns it multiplies, and then which of two obstacles it
met. A goal with hypotheses hears that the hypotheses multiplied reach three. A goal with none hears
that the pool the products are built from is empty, so no degree of them exists, because telling
that author about the degree would send them to restate a goal when what it lacks is a premise.

**A product of two variables is an atom, and the hypotheses are multiplied to reach it.** No
combination of forms over `x` and `y` gets to an atom `x * y`, so `0 < x /\ 0 < y ==> 0 < x * y`
was refused although it is an axiom. Every pair of hypotheses is now multiplied, itself included,
and the products are offered to the ordinary certificate search as facts of their own, which is the
move `nlinarith` makes over `linarith`.

```scala
Linarith.standard.prove("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y")
Linarith.standard.prove("!x:real. 0 < x ==> 0 < x * x")
Linarith.standard.prove("!x:real y:real. 1 < x /\\ 1 < y ==> 1 * 1 < x * y")
```

**It happens second, and only when the linear search has failed.** The pairs are quadratic in the
hypotheses, so the linear program grows; a goal decided without them costs what it always cost, and
a chain of twelve is 5 ms either way. Measured on 2026-09-09, the retry takes a refusal from 5 ms to
32 ms at twelve hypotheses and from 5 ms to 22 ms at ten, which is the size of a real goal.

**Every pair of inequalities is multiplied, and the last of the three needed a lemma.** `LT_MUL`
gives a strict product from two strict facts, `Order.MUL_NONNEG` a non-strict one from a strict and
a non-strict, and `Order.MUL_NONNEG_BOTH` a non-strict one from two non-strict. The third pair was
skipped until 2026-09-10, and this file called it a missing lemma rather than a missing move: that
turned out to be exactly right, since nothing in the procedure changed when the lemma arrived except
the line that picks which one to instantiate. What the lemma costs is a case analysis on `LE_CASES`,
where a factor that is zero makes the product zero and a factor that is positive is the mixed lemma
already there.

**An equality is paired too, through its two halves, and what that replaced was an argument that is
wrong.** The argument said: the difference an equality states is zero, so every product with it is
zero and carries nothing a combination could use. The first half is true and the second does not
follow. `e = 0` times `0 < n` is `n * e = 0`, which is zero and which says that *the atom* `n * e`
is zero, and the linear reading had no other way to know that, since `n * e` is a column of its own
and nothing else constrains it. That is why `n * d = b /\ 0 < n /\ 0 < b ==> 0 < d` was refused, and
it is proved now. The halves are `a <= b` and `b <= a`, reached by `Order.LE_OF_EQ` both ways round,
so this needs no lemma that did not already exist and reaches no new axiom; they are used for
pairing and are not added to the facts, since as forms they say what the equality already said.

```scala
Linarith.standard.prove("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 <= x * y")
```

A non-strict pair still cannot reach a strict conclusion. `0 <= x ==> 0 < x * x` is refused, which is
the same boundary the second phase of `Farkas` keeps one level down.

Nothing about this can make the procedure wrong. A manufactured fact is a theorem like any other and
the ring step still checks the combination against the goal, so a product that helps nothing costs a
refusal.

**A quotient by a numeral is a coefficient, and was an atom until 2026-09-09.** `x / 3` is `x` at a
third of the way, so `eps / 3 + eps / 3 + eps / 3 <= eps` is proved and `3967 / 285489 < 14 / 1000`
is decided as written rather than cross-multiplied first. Zero is not a denominator, which is the
rule `Ring` already keeps: `x / 0` is an atom and the refusal says so. A symbolic denominator is an
atom too, and it stays one: turning `inv y` into anything needs `~(y = 0)`, which is `Field`'s to
charge for and not this procedure's.

```scala
Linarith.standard.prove("!e:real. e / 3 + e / 3 + e / 3 <= e")
Linarith.standard.prove("3967 / 285489 < 14 / 1000")
```

**A non-strict hypothesis never becomes a strict conclusion.** `x <= y ==> x < y` is false at
`x = y`, and what keeps it out is that a combination has to weigh some strict fact, or the
constant, above zero before it can prove anything strict. A feasible set of multipliers chosen
without asking may weigh none of them, so the search asks: that is the second phase in `Farkas`,
and it is the only place where the two kinds of inequality are told apart.

**The multipliers are rational and no theorem ever sees a fraction.** A certificate is cleared of
its denominators before anything is proved, so what the kernel is shown is a sum of whole multiples
of the hypotheses, and what that sum equals is the goal's difference multiplied by the common
denominator. `Order.cancelPositive` takes that multiplier back off. So `2 * x < 2 * y ==> x < y`,
which needs the multiplier one half, is proved by multiplying the goal by two, and no multiplier
ever reaches the kernel as a fraction. What the goal itself is written with is a different matter:
`Ring` reads a denominator that is any non-zero constant as a rational coefficient, so a goal may
carry one and the ring step will check it.

The search runs on linear forms extracted from the terms, in ordinary arithmetic, with no theorem
near it. A wrong answer from it makes the checking step refuse, so the worst it can do is fail to
find a proof.

**A proof will say what it rests on.** A sequent carries the premises that were assumed rather than
the ones that were needed, which is an upper bound; the certificate knows the difference, because a
hypothesis weighed by zero took no part:

```scala
Linarith.standard.support("x:real < y:real /\\ z:real < w:real /\\ y:real < z:real ==> x < z")
// Right(Support(hypotheses = Vector((x < y, 1), (y < z, 1)), squares = Vector()))
```

Two of the three premises, with their weights, and `z < w` named as carrying nothing. That is the
question an argument gets asked: not whether it follows, but which of its assumptions it needed.

The second field is empty here and is not decoration. Since 2026-09-18 the procedure may give
itself one fact nobody wrote, a square completed over a quadratic atom, and a goal settled with
one rests on something that is in no premise. Reporting it among the premises would answer a
question nobody asked; leaving it out would make such a proof report an empty list, which is
already what a goal needing none of its premises reports. So it comes back beside them, and
`docs/adr/0032` is the decision.
The premises come back in the words they were written in when the goal has free variables, which is
what a claim about named quantities is; a goal with leading quantifiers comes back with the
variables the procedure opened them into, because a bound variable has no name in a term.

### `Arithmetic` — numerals

```scala
Arithmetic.standard.add(1000, 1000)      // |- 1000 + 1000 = 2000
Arithmetic.standard.multiply(3, 4)       // |- 3 * 4 = 12
```

Digit by digit, through eleven lemmas that are themselves proved from the axioms. What it costs
follows the number of digits rather than the size of the numbers, and the rate was measured on
2026-09-05 by bisecting on the pass budget: about three passes per digit for a sum and six and a
half for a product, so the twelve-digit product `Oracle.NumeralBudget` allows takes eighty. The
budget is four hundred.

### `Order` — where the numerals meet the order

The five order axioms are relational: each says how `<` survives an operation, and none of them
says that any particular number is below any other. So `0 < 1` is something to prove rather than
something the theory hands over, and every inequality between two numerals is downstream of it.

```scala
Order.standard.zeroLessOne     // |- 0 < 1
Order.standard.positive(12)    // |- 0 < 12
Order.standard.less(53, 60)    // |- 53 < 60
```

`0 < 1` is proved by cases on trichotomy at `0` and `1`. The middle case contradicts
`ONE_NOT_ZERO`; the third does not rule its case out but proves the goal inside it, because a field
where `1 < 0` is a field where `-1` is positive and the square of a positive is positive.

`positive` climbs the binary encoding rather than counting: `BIT0 k` is `k + k` and `BIT1 k` is
`(k + k) + 1` by definition, and a sum of positives is positive, so one step per bit gives `0 < n`
from `0 < 1`. The cost follows the number of digits and not the value, which is why `0 < 10^24` is
a fifth of a second and not a wait: measured on 2026-09-05, 9 ms at ten bits, 77 ms at forty and
225 ms at eighty.

`less` works out the difference on the numerals first, proves that positive, and adds the smaller
numeral back to both sides with `LT_ADD`. What the ring step then sees is an identity between two
numerals rather than a cancellation.

**Decides:** `0 < n`, and `m < n`, for numerals.
**Refuses:** zero and anything below it, and a comparison that is false as stated.

Besides the numerals it holds the order lemmas that need more than one axiom and are wanted in
more than one place. Each is proved, and `OrderSpec` prints every one of them:

| Fact | Statement, as it prints |
|---|---|
| `ZERO_LT_ONE` | `0 < 1` |
| `ADD_POSITIVE` | `!x y. 0 < x ==> 0 < y ==> 0 < x + y` |
| `LT_TO_ZERO` | `!x y. x < y ==> 0 < y - x` |
| `LT_FROM_ZERO` | `!x y. 0 < y - x ==> x < y` |
| `POSITIVE_NOT_ZERO` | `!x. 0 < x ==> ~(x = 0)` |
| `CANCEL_POSITIVE` | `!x y. 0 < x ==> 0 < x * y ==> 0 < y` |
| `LT_MUL_BOTH` | `!x y z. 0 < x ==> y < z ==> y * x < z * x` |
| `LE_MUL_BOTH` | `!x y z. 0 <= x ==> y <= z ==> y * x <= z * x` |
| `INV_POSITIVE` | `!x. 0 < x ==> 0 < inv x` |
| `INV_ANTITONE` | `!x y. 0 < x ==> x <= y ==> inv y <= inv x` |
| `LE_OF_LT` | `!x y. x < y ==> x <= y` |
| `LE_OF_EQ` | `!x y. x = y ==> x <= y` |
| `LE_CASES` | `!x y. x <= y ==> x < y \/ x = y` |
| `ADD_NONNEG_LT` | `!x y. 0 <= x ==> 0 < y ==> 0 < x + y` |
| `ADD_NONNEG` | `!x y. 0 <= x ==> 0 <= y ==> 0 <= x + y` |
| `MUL_NONNEG` | `!x y. 0 < x ==> 0 <= y ==> 0 <= x * y` |
| `MUL_NONNEG_BOTH` | `!x y. 0 <= x ==> 0 <= y ==> 0 <= x * y` |
| `CANCEL_NONNEG` | `!x y. 0 < x ==> 0 <= x * y ==> 0 <= y` |
| `LE_TO_ZERO` | `!x y. x <= y ==> 0 <= y - x` |
| `LE_FROM_ZERO` | `!x y. 0 <= y - x ==> x <= y` |
| `LE_ANTISYMMETRIC` | `!x y. x <= y ==> y <= x ==> x = y` |
| `SQUARE_NONNEG` | `!x. 0 <= x * x` |
| `ADD_LE` | `!x y z u. x <= y ==> z <= u ==> x + z <= y + u` |
| `LE_OF_NOT_LT` | `!x y. ~(x < y) ==> y <= x` |
| `LT_OF_NOT_LE` | `!x y. ~(x <= y) ==> y < x` |

The last two turn a negated comparison into a positive one and cost nothing classical, which is
the thing to know about them: on this order `LT_TOTAL` puts all three cases on the table before
anything is negated, so the negation only discards one of them. `OrderSpec` asserts that they rest
on trichotomy and on nothing else, because the natural assumption is that the excluded middle is in
there somewhere and it is not.

The ten that mention `<=` are all downstream of one thing: `<=` is an abbreviation for
`x < y \/ x = y` and carries no axiom, so each of them is a case analysis on that disjunction where
one branch is the strict fact above it and the other is a rewrite. `LE_CASES` is the way in and
`LE_OF_LT` and `LE_OF_EQ` are the ways out. `LE_ANTISYMMETRIC` is the one that goes the other way,
from two bounds to an equality, and it is how `Linarith` proves a goal that is an equation.

`SQUARE_NONNEG` also mentions `<=` and is the one fact here that is not downstream of that
disjunction: its case analysis is on trichotomy at `0` and `x`, and all three branches prove the
goal rather than two of them refusing their own case. `LT_MUL` gives a positive product from two
positive factors and says nothing about a factor that is negative or zero, so `0 <= x * x` for
*every* `x` is not an instance of any axiom. The negative branch is the one to read: `LT_ADD` moves
`x < 0` to `0 < -x`, `LT_MUL` gives `0 < -x * -x`, and one ring identity says that is `x * x`. So
the strictly positive cases are the positive and the negative one, and zero is the only case that
needs `<=` at all. The strict form `0 < x * x` is false at zero and is not here; a caller holding
`~(x = 0)` gets it from this and `LE_CASES`.

`ADD_LE` is what the axioms leave out. `LT_ADD` adds the *same* term to both sides of *one*
inequality; adding two inequalities together is a different move, and it is the one every bound
assembled out of parts needs. Both premises go to the form `0 <= e`, `ADD_NONNEG` adds them, and
the ring supplies `(y - x) + (u - z) = (y + u) - (x + z)`.

The letters are the printer's rather than the source's: bound variables have no names in the terms
at all, and `Printer` invents `x, y, z, u, v, w` by depth, so the positive factor that `Order` calls
`c` prints as `x` in the two lemmas where it is bound first, and `ADD_LE`'s fourth variable prints
as `u`.

`INV_POSITIVE` is what a ratio between two measured quantities needs. It was **the only** fact here
that mentioned `inv` until 2026-09-18, and that sentence is one of five that said so; `INV_ANTITONE`
is the second, and it is the one that says the reciprocal reverses the order. Neither `Ring` nor
`Linarith` can produce either: both treat `inv x` as an atom they know nothing about, which is also
what makes the derivation of `INV_ANTITONE` work, since the one thing it needs about inverses
arrives as a rewrite from `MUL_INVERSE` rather than from a normal form. `Field` is the other one
that knows something about `inv`, and what it knows costs a hypothesis.

`CANCEL_POSITIVE` is the one to read twice. It divides by a positive number without dividing: the
proof is a case analysis on trichotomy, where `x = 0` makes the product zero and `x < 0` makes
`c * -x` positive and the two products cancel to `0 < 0`. That is what will let a certificate with
rational multipliers be checked after clearing its denominators, in a development where the ring
normalisation cannot cancel one.

A fact is used by specialising it and discharging its premise, which is where the numerals meet the
lemmas:

```scala
val order = Order.standard
val rules = order.reals.logic.rules

for {
  two <- order.reals.term("2")
  positive <- order.positive(2)      // |- 0 < 2
  lemma <- order.inversePositive     // |- !x. 0 < x ==> 0 < inv x
  atTwo <- rules.spec(two, lemma)
  result <- rules.mp(atTwo, positive)
} yield result
// Right(|- 0 < inv 2)
```

## Using a lemma the development already holds

The example above specialises a lemma at `2` because somebody wrote `2`. `Apply` is the same step
with the somebody removed: give it a lemma and a goal, and it decides what the lemma's variables
have to be for its conclusion to **be** the goal.

```scala
val reals = Order.standard.reals
val logic = reals.logic.over(reals.theory).toOption.get   // see below

for {
  goal <- reals.proposition("0 < inv 2")
  lemma <- Order.standard.inversePositive     // |- !x. 0 < x ==> 0 < inv x
  used <- Apply.to(logic, lemma, goal)
} yield (used.obligations, used.theorem.conclusion)
// obligations: Vector(0 < 2)
// conclusion:  0 < 2 ==> 0 < inv 2
```

It hands back what is left to prove rather than proving it. A caller that discharges the
obligations reaches the goal with `rules.mp`; a caller that cannot has learned what the lemma would
have cost, which is more than a refusal tells them.

**The widening is not optional and the reason is worth knowing.** `Real.standard` sits over
`Logic.standard`, which has no axioms and has never heard of the type operator `real`. Specialising
a universal means asking the theory for the quantifier constant *at the type it ranges over*, so
without `.over(reals.theory)` every application refuses with "no type operator named real in this
theory" and the library looks empty rather than unreachable.

### The one that could not be used before

`COMPLETENESS` is the only one of the sixteen axioms that quantifies over a predicate, and the only
one that separates the reals from the rationals. Everything else in this development is true of the
rationals word for word.

Using it means deciding what its `P` is, and `P` occurs in it applied to a bound variable. That is a
**Miller pattern**, `Matching` was first order until 2026-09-11, and so the axiom could be used only
by somebody writing the predicate out themselves. Nobody ever did.

```scala
val goal = reals.proposition(
  "?s:real. (!x:real. x < 1 ==> x <= s) /\\ (!b:real. (!x:real. x < 1 ==> x <= b) ==> s <= b)")

Apply.to(logic, reals.axioms("COMPLETENESS"), goal.toOption.get)
// the instantiation says  P := \x:real. x < 1
// the obligation says     (?x:real. x < 1) /\ (?x:real. !y:real. y < 1 ==> y <= x)
```

`CompletenessSpec` in `modules/theories` runs that through to a theorem: the witness for "there is
an upper bound" is `1`, and that it *is* one is LINARITH's to say. Seven and a half thousand
inferences over twelve axioms, completeness among them, and nobody wrote `\x. x < 1`.

**What the fragment does not do.** Full higher-order unification is undecidable and is not here. A
pattern variable applied to something that is not a bound variable, or to the same one twice, has
several answers and this returns none of them, which is a refusal rather than a guess. And the
first-order answer wins wherever there is one, so `\x. F x` against `\x. sin x` still gives
`F := sin`.

### The one that could not be used at your type

A lemma stated over a type variable applies at every type, and until 2026-09-12 the lookup could not
see that. `FST_PAIR` is `!x:'a. !y:'b. FST (PAIR x y) = x`; the goal `!x:num. !y:num. FST (PAIR x y)
= x` **is** that lemma at `num`, and asking for it was refused, because `Const("FST", prod('a,'b) ->
'a)` and `Const("FST", prod(num,num) -> num)` are different terms and the match failed on the head
before it reached an argument. Fourteen lemmas arrived over a type variable that week and none of
them could be applied to anything.

`Matching.matchTerm` now answers with a type substitution beside the term one, the way HOL Light's
`term_match` does, and it is the same one-way question: only type variables occurring in the
**pattern** may be solved, the target's types are fixed, and one type variable cannot be solved two
ways over one walk. `Apply` instantiates the lemma's types before specialising it at the terms, so
what comes back is a theorem about `num` rather than a theorem about `'a` that happens to print
like one.

```
sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:num. !y:num. FST (PAIR x y) = x"
// proved, 1126 inferences over 1 axiom: the projections are defined by choice
```

The range of that type substitution is read off the goal, and a goal reaches the prover having been
type-checked by `Theory.checkType` as it was read, so no type operator nobody declared enters a
theorem this way. `Matching.Instantiation.instance` carries that argument where the code is.

### The one that cannot be used at a second argument, and will not be

The two above were gaps that got closed. This one is not a gap: it is what declaring a constant
costs, it is permanent, and the only thing to do about it is to know it before you write the theory
rather than after.

`Kernel.inst` substitutes **free variables**. Its docstring says so and is accurate. The consequence
nobody states is the other half: a constant is a position no instantiation will ever reach. Whatever
you declare, you have decided cannot vary; whatever you leave a free variable, a development three
links down can still specialise.

That is invisible while you are writing one theory, because inside one theory both read the same.
It becomes visible the first time something wants the same derivation at a second argument. On
2026-09-12 a consumer had two aggregates of identical mathematical shape, each a generating function
evaluated at a point:

- the first evaluated at `z = 3`, where `z` was a free variable of the derivation, so the existing
  derivation was reused by instantiating it, and
- the second evaluated at `z = 1`, where the corresponding position held a **declared constant**, so
  there was nothing to instantiate and the derivation had to be redone.

The mathematics does not distinguish those two cases at all. The kernel distinguishes them
absolutely, and in the direction that is easy to get backwards: the thing that looks more solid,
the named constant, is the one you can do less with.

The rule of thumb that falls out, and it is about the moment before the theory exists: **declare
what the development is about, and leave what it is parameterised by a free variable**, even when
there is one caller and the parameter has one value. `Series` is the worked example on the right
side of this. `SUM_LINEAR` takes its scalar as `!a`, not as a declared constant, and that is why
`SUM_CONSTANT` could be stated over `!c:real` at all rather than once per constant somebody wanted
to sum.

### Every lemma that applies

```scala
Apply.candidates(logic, Order.standard.facts.toVector, goal)
// the ones whose conclusion is this goal, fewest obligations first
```

`Prove` asks this before it asks any decision procedure, over the facts of the developments it was
built on. **`Prove.construct(chain)` is the one to reach for when you have a chain**: `Prove.standard` is
over the reals alone, so a goal mentioning `num` cannot even be stated to it and none of the
naturals' lemmas is in the library it can reach. That is why `!x:real. 0 <= x * x` was
the first goal the lookup settled: it is `SQUARE_NONNEG`, and until the lookup existed the answer
was "nobody here can do this" from a system holding the lemma four lines away, because LINARITH
then took no goal whose atom is a product of unknowns without hypotheses to multiply. Since
2026-09-18 it takes this one as well, by completing the square, and the lookup is still asked
first.

### Asking whether a set of rules can all hold

`Consistency` decides the propositional fragment and **proves nothing**. It stands where
`Refutation` and `Quantified` stand, under `docs/adr/0005`: something answers, nothing is certified,
and a test scans the file and fails if it names an inference rule.

```scala
Consistency.standard.reading(Vector("p:bool ==> q:bool", "q:bool ==> r:bool", "p:bool", "~(r:bool)"))
// Contradictory: no assignment satisfies them, so they cannot all hold
```

The question it exists for is the one somebody asks of a formalised register of rules: **do two
rules oblige and forbid the same thing?**

**The two answers are not two sides of one coin.** `Contradictory` is a decision about the world: if
no assignment of truth values works, the premises cannot all hold whatever the atoms mean, because
every real situation induces some assignment. `NotContradictory` is about propositional structure
only — the atoms are uninterpreted, so `x = y` and `y = x` are two of them, and a set it accepts may
still be unsatisfiable for a reason living inside an atom. That is why the name is not "consistent".

A quantifier is refused by name. `!x. p x` is a proposition and is not a connective, so a reader
looking for maximal non-connective subterms would take it as an atom, miss a genuine contradiction,
and report the weak answer about premises that cannot hold.

## Proving: by hand

The derived rules are on `Logic.standard.rules`. They are the ordinary ones, each derived from the
kernel's ten:

| Rule | From | To |
|---|---|---|
| `conjIntro` | `G ⊢ p`, `D ⊢ q` | `G, D ⊢ p /\ q` |
| `conjElim1`, `conjElim2` | `G ⊢ p /\ q` | `G ⊢ p`, `G ⊢ q` |
| `disch(p, th)` | `G ⊢ q` | `G - {p} ⊢ p ==> q` |
| `mp` | `G ⊢ p ==> q`, `D ⊢ p` | `G, D ⊢ q` |
| `gen(x, th)` | `G ⊢ p`, `x` not free in `G` | `G ⊢ !x. p` |
| `spec(a, th)` | `G ⊢ !x. p` | `G ⊢ p[a/x]` |
| `notIntro`, `notElim` | around falsity | `~p` |
| `eqTruthIntro`, `eqTruthElim` | `G ⊢ p` | `G ⊢ p = T` |
| `disjIntro1(q, th)`, `disjIntro2(p, th)` | `G ⊢ p`, or `G ⊢ q` | `G ⊢ p \/ q` |
| `disjElim(d, l, r)` | `G ⊢ p \/ q`, `D ⊢ c`, `E ⊢ c` | `G, D - {p}, E - {q} ⊢ c` |
| `existsIntro(P, a, th)` | `G ⊢ P a` | `G ⊢ ?x. P x` |
| `existsElim(e, v, th)` | `G ⊢ ?x. P x`, `D ⊢ c` with `P v` in `D` | `G, D - {P v} ⊢ c` |
| `proveHyp(th, target)` | `G ⊢ p`, `D ⊢ q` | `G, D - {p} ⊢ q` |

Two of these carry side conditions, the universal introduction and the existential elimination, and
they are where a proof by hand goes wrong.

`gen` needs its variable to be free in no hypothesis, which the kernel checks on abstraction.

`existsElim(e, v, th)` needs `v` to be free in nothing but the instance `P v` it discharges, which
is three conditions rather than one. Free in the rest of `D` is the kernel's, inherited through the
generalisation the rule performs. Free in `c`, or free in the predicate `P`, are checked by the rule
and refused with `EscapingVariable`, which names which one failed. They are checked rather than left
to surface downstream because they would not surface: generalising closes over those occurrences
too, the antecedent then no longer matches, and nothing in `mp` compares antecedents, so what would
come back is a true sequent carrying an extra hypothesis instead of an error. The hypotheses `G` of
the existential itself are unconstrained: `v` may occur there freely.

`existsElim` also refuses a case that does not assume the instance, with `MissingHypothesis`. That
one is not a soundness condition, and it is where the two eliminations differ deliberately:
`disjElim` accepts a branch that never used its disjunct, because such a branch still proves the
conclusion. Here the same permissiveness would return the conclusion with the existential added as a
premise that did nothing, which is what passing the wrong witness looks like, and it looks like
success.

Disjunction and the existential are still definitional, and every rule above is still a derivation
from the kernel's ten that needs no axiom. What changed on 2026-09-10 is that `p \/ ~p` is now
reachable, so a proof by cases no longer has to find its disjunction in the theory it is about. The
rules are on `Classical.standard` rather than on `Logic.standard`, because they cost an axiom and
`Logic.standard` is the one that costs nothing:

| Rule | From | To |
|---|---|---|
| `excludedMiddleAt(p)` | | `⊢ p \/ ~p` |
| `cases(p, positive, negative)` | `D ⊢ c`, `E ⊢ c` | `D - {p}, E - {~p} ⊢ c` |
| `contradiction(p, th)` | `G ⊢ F` | `G - {~p} ⊢ p` |
| `ext(th)` | `G ⊢ !x. f x = g x` | `G ⊢ f = g` |

`cases` is the one most derivations want, and it is why the axioms are worth their cost: until it
existed, `LT_TOTAL` was the only supplier of a case split in this system, which meant a case split
could only be made about an order and never about a proposition. `contradiction` is the converse of
`falsityElim`: that rule gives anything from falsity and is intuitionistic, this one gives `p` from
the absurdity of `~p` and is not. `ext` is function extensionality, and what it removes is in
[what is missing](#what-is-missing-and-the-order-to-add-it) below, under `SUM_CONGRUENCE`.

Three refusals are worth knowing. `cases` refuses two branches that prove different conclusions,
which is `disjElim`'s check arriving through it. `contradiction` refuses a theorem that does not
prove falsity. `ext` refuses a body that is not two functions applied to the quantified variable:
`!x. f x = c` is a true statement of a shape eta cannot close, and closing it anyway would give a
theorem about `\x. c` rather than about `c`.

A proof by hand chains them. This one takes commutativity of addition and specialises it twice:

```scala
val reals = Real.standard
val rules = reals.logic.rules
val a = Term.variable("a", TyApp("real", Nil))
val b = Term.variable("b", TyApp("real", Nil))

for {
  commutativity <- reals.axiom("ADD_SYM")
  atA <- rules.spec(a, commutativity)
  atB <- rules.spec(b, atA)
} yield atB
// Right(|- a + b = b + a)
```

A proof by cases assumes the disjunction, proves the same conclusion twice, and hands both to
`disjElim`, which discharges one disjunct from each branch:

```scala
val logic = Logic.standard
val rules = logic.rules
val p = Term.variable("p", Type.Bool)
val q = Term.variable("q", Type.Bool)

for {
  disjunction <- logic.mkDisj(p, q)
  assumed <- LogicError.lift(Kernel.assume(disjunction))
  fromLeft <- LogicError.lift(Kernel.assume(p)).flatMap(rules.disjIntro2(q, _))
  fromRight <- LogicError.lift(Kernel.assume(q)).flatMap(rules.disjIntro1(p, _))
  eliminated <- rules.disjElim(assumed, fromLeft, fromRight)
  theorem <- rules.disch(disjunction, eliminated)
} yield theorem
// Right(|- p \/ q ==> q \/ p)
```

That one assumes its disjunction. Since 2026-09-10 a proof by cases can prove the disjunction
instead, which is the shape every tactic that wants to know whether something holds before reasoning
about it will use:

```scala
val classical = Classical.standard
val logic = classical.logic
val rules = logic.rules
val p = Term.variable("p", Type.Bool)

for {
  notP <- logic.mkNot(p)
  positive <- LogicError.lift(Kernel.assume(p)).flatMap(rules.disjIntro1(notP, _))
  negative <- LogicError.lift(Kernel.assume(notP)).flatMap(rules.disjIntro2(p, _))
  theorem <- classical.cases(p, positive, negative)
} yield theorem
// Right(|- p \/ ~p)
```

Both branches are discharged, so nothing is left in the hypotheses. `ClassicalSpec` runs this.

For equational steps, `Rewrite` places an equation inside a term and proves the result equal, and
`Conv` carries the small steps: `sym`, `trans`, `apTerm`, `apThm`, beta normalisation, and
unfolding a definition.

## Proving: with the algebra half

The bridge asks the algebra for an answer and proves it.

```scala
import garden.xeno.symbolum.tactics._
import garden.xeno.symbolum._, garden.xeno.symbolum.Dsl._

val x = Var("x")
Oracle.standard.certifyExpansion((x + 1) * (x + 1))
// Right(Certified(..., theorem))
```

The outcomes are a theorem or no theorem. There is no third case where the algebra persuades
anybody of something false, and the test that earns the module is the one where it is wrong on
purpose.

The discovery loop screens candidate identities numerically and certifies the survivors:

```scala
val candidates = Vector((x + 1) * (x + 1), x*x + Num(2)*x + Num(1), x*x + Num(1))
Discovery.standard.identities(candidates, Discovery.grid(candidates, 100))
// Proved(...), Disproved(..., witness), ...
```

**The screen has two stages and the kernel is the third thing.** `Double` first, at
`Discovery.Tolerance` of 1e-8, which throws away almost everything for almost nothing. Then fifty
digits, over `Precise`, run only on what the first stage could not separate. `docs/adr/0011` is the
decision and the argument, including why the two stages report different outcomes.

Four outcomes, and the last is where the attention goes:

| outcome | what it says |
|---|---|
| `Proved` | certified by the kernel |
| `Disproved` | the first stage found a point, at sixteen digits |
| `Separated` | the first stage could not, the second could, and it carries how many digits they agreed to |
| `Unsettled` | true at every point tried, at fifty digits, and not turned into a theorem |

`Separated` and `Disproved` are the same verdict in the ledger and not the same fact. A candidate
the `Double` stage separates was written wrongly; one that needed fifty digits agreed to forty-odd
everywhere it was asked, which is either a near-identity worth reading or the false positive the
second stage was built for, and the number of digits is what tells them apart.

`Unsettled` carries how many points it survived, because agreement at three points is nothing and
agreement at three hundred is a lead.

It also carries **which of four situations** it was, and only one of them is that lead:

| `Why` | What it says | What to do about it |
|---|---|---|
| `OutsideTheFragment` | `Translate` refused by name: a cosine, a root, an exponent it will not expand | nothing, or widen the theory |
| `BeyondTheBudget` | sayable, and carrying a numeral whose arithmetic costs more than the caller should wait for | raise `Oracle.NumeralBudget` and wait |
| `RewriterRanOut` | the normalisation stopped at its step limit, so the two sides differing means nothing | raise the limit |
| `NotProvableHere` | both sides reached a normal form, the forms differ, and it agreed at every point anyway | **look**: either the mathematics is missing, or the agreement was a coincidence over the sample |

The first three are the machinery describing itself. Before they were separated they arrived as
one bucket with the fourth, and a run could not be read.

## Refuting: asking a model instead of a tactic

A tactic that will not prove something tells you nothing about why. A model tells you where it
fails, and it is the same idea one level up from the discovery loop: `Evaluate` says what a term
denotes under a choice of what the constants mean, and `Refutation` looks for the assignment that
settles the question.

```scala
val premise = reals.proposition("0 < x:real")
val claim = reals.proposition("1 < x:real")
Refutation.standard.counterexample(Vector(premise).map(_.toOption.get), claim.toOption.get)
// Solved(Map("x" -> 1))
```

The witness is the point: `0 < 1` holds and `1 < 1` does not, so the entailment is false, and a
reader can check that without trusting anything in this repository. It is `1` rather than something
strictly between the two bounds because the solver returns a vertex of the region rather than an
interior point, and a vertex is where a linear program stops.

The same search answers the question a sequent cannot ask about itself. `h1..hn |- c` is true
whenever the premises contradict each other, and the kernel will prove both `H |- c` and `H |- ~c`
without complaint, because both are correct. So before believing what a set of hypotheses implies,
ask whether anything satisfies them:

```scala
val cycle = Vector("x:real < y:real", "y:real < z:real", "z:real < x:real")
Refutation.standard.satisfying(cycle.map(text => reals.proposition(text).toOption.get))
// Contradictory(3): no assignment satisfies them, and this one is decided rather than sampled
```

**Where the premises are linear, this is solved rather than sampled.** A set of linear premises
over the reals is a system, and whether anything satisfies it has a finite answer either way, which
`Linarith` already had the machine for. So `{x = 1}`, which a sampler lands on with probability
zero, comes back as `Solved(x = 1/1)` with the point; `{2 * x = 1}` comes back with a half, exactly,
as a rational rather than as something near it; and the cycle above comes back as a decision. That
is what a corpus of measurements needs, because a measurement is an equality and an equality was
the shape the sampler had to decline.

**What the solver will read is narrow, and the rule is the whole of it.** An atom is admitted only
when it is a free variable of type `real`, so a premise is a constraint of the system only where
every atom of it is one, and a product of two unknowns is never answered with a rational.

**The premises are partitioned rather than judged together, since 2026-09-11.** Until then one
premise the solver could not read sent every other premise to the sampler, and a claim about a
domain is written exactly the other way round: some constraints over the reals and some over a
declared type. The premises the solver can read are one system; the rest are evaluated at each
assignment of their own free variables over the carriers the model sized. The two halves share no
variable, because an atom of the system is of type `real` and `real` has no carrier, so the system
is solved once and the enumeration decides the rest.

```scala
// `risk : entity -> real`, over a model that sizes `entity` at three, and `reads` is that
// theory's parser, since what this takes is propositions rather than text
search.satisfying(Vector("0 < x:real", "x:real < 1", "risk a < risk b").map(reads))
// Solved(x = 1/2, a = entity#0, b = entity#1): Survived(100) until 2026-09-11
```

`Contradictory` stays a decision and never becomes a count: it is reported where **every**
assignment was evaluated and none was feasible, or where the system alone has no point. One
assignment this model could not evaluate sends the question back to the sampler with the answer the
sampler has. Over a declared type it is a decision about **this** model, which is what every answer
here is: nine pairs sized at three, all nine put.

What is still sampled is what is neither a constraint nor enumerable: a product of two unknowns, a
variable of type `num`, which is sampled rather than enumerated, a declared type nobody sized, and
an enumeration larger than `Refutation.Assignments`.

The proof side is not held to the atom rule and has not been since 2026-09-10, when
`Linarith` began multiplying a product of two unknowns out and weighing the result as an atom of
its own. Nothing is proved about what an atom denotes, so the step is sound whatever it denotes; a
witness has to denote, and a point that gives `x * y` a value unrelated to the ones it gives `x`
and `y` does not satisfy the premises it was found for. `docs/adr/0005` records that asymmetry as a
decision rather than as a limit more work removes.

Seven outcomes, and telling them apart is the whole point of the file:

| Outcome | What it says |
|---|---|
| `Solved` | a point where every premise holds, found by solving. Exact, and the values are rationals, with the inhabitants of any sized type beside them |
| `Contradictory` | there is no such point at all: the premises cannot all hold. A decision, not a count of failures |
| `NoCounterexample` | nothing satisfies the premises together with the denied conclusion, so the entailment holds over this fragment |
| `Found` | a point, found by sampling. It answers, and it is a fact about one model |
| `Survived` | every point answered and none was the one wanted, with the count, because no witness at four points and no witness at four hundred are different findings |
| `NeverAsked` | no point could be evaluated at all, which is what happens to a universally quantified premise over the reals: there is no finite domain to enumerate and one sample point would prove nothing |
| `Undecided` | the refusal. A premise that pins an equality and is not part of a linear system is satisfied on a set a sampler never lands on, and reporting `Survived` there would say the same thing about `{x = 1 /\ 0 < x}` as about `{0 < x, x < 0}` while one of the two is satisfiable |

An equality that has to be **false**, such as `~(x = 0)`, trips none of this: it is true almost
everywhere, which is where a sampler already looks.

**And the refusal is about the coordinates, not about the type**, since 2026-09-11. It used to ask
whether the equality's type had a finite carrier, which was the same question while the reals were
the only thing sampled. Now `num` is sampled too, as a small range of whole numbers: `x:num = y:num`
has no finite carrier and the grid lands on it about one point in twelve, and `real_of_num n = 3` is
an equality **between reals** that is true at one of the naturals the grid draws. Both came back
refused. What makes an equality unreachable is a coordinate drawn from a continuum, and that is what
the question asks now.

**The naturals are sampled too, since 2026-09-11, and nothing about them is enumerated.** The model
used to interpret the seven constants the theory of the reals declares and nothing else, so a claim
naming `Sum`, `Power`, `Prod`, `SUC`, `NUM_ADD`, `NUM_MUL`, `NUM_LE` or `real_of_num` had no point
that could be evaluated at all and came back `NeverAsked`. Measured on that day over this
repository's own proposal audit, then 116 proposals: nineteen named one of those and not one of
them carried a witness, and sixteen did once the naturals were sampled.

```scala
Refutation(Evaluate.over(chain.reals, Model.Numbers))
  .counterexample(Vector.empty, claim)   // !x:num y:num. real_of_num (x + y) = real_of_num x * real_of_num y
// Found(x = 4, y = 8)
```

**There is no carrier for `num`, and that is the decision rather than an omission.** A finite
carrier would make a universal over the naturals enumerable and would make the model lie: with a
successor that saturates at the top element, `!n. ~(SUC n = n)` comes back false, and a model that
refutes a theorem is worse than no model. With a successor undefined at the top, no universal that
mentions one has a value. So `num` is treated the way `real` already is: not enumerated, sampled,
and a point that turns up is a genuine natural and therefore a genuine witness. `RefutationSpec`
puts every lemma of the standard library to the model and asserts that none of them is refuted.

A variable of type `num -> real` is sampled as a **function**, because six of those nineteen
proposals quantify over a summand rather than over a number and `!f n. 0 <= Sum f n` cannot be
refuted by an assignment with nothing to put in `f`. The sampled function is a function and not a
table: asked twice about one index it answers the same way, which is what makes the witness one.
Witnesses print as their first few values, `<-0.51, -1.12, -1.72, -2.32, ...>`, because a witness
nobody can inspect is a rumour.

**Where the arithmetic is exact, a point is a verdict.** Over the reals a sampled counterexample can
be a rounding artefact, which is why nothing here promotes one; over the naturals it cannot, because
`Model.Numbers` computes them on `BigInt`. So `Abduce.Gap.decisive` says whether the point settles
the claim, and `Cost` reports `Fails` when it does. Five proposals of this repository's own audit
moved out of `Unreadable` that way: they are claims wholly about the naturals or about truth values,
they are false at a small number, and "nobody here can take this shape" was the least useful true
thing that could be said about them.

The test is syntactic and conservative. Every constant has to be one the model computes exactly and
every variable and binder has to be at a type it holds exactly, so a claim mentioning `real_of_num`
fails it even though its naturals were exact going in, because the answer came out as a `Double`.
`Refutation.Solved` is exact as well, and is deliberately not counted: its values are rationals
satisfying a linear system over the reals, and promoting that is a second question.

The rest stay `Open`, which is right: a standing is about what a *procedure* settles, and no
procedure here reads `num`. What changed for those is that the report now says where the claim fails.

**A variable the search cannot sample is left out of the point rather than given a real.** That was a
defect until 2026-09-11: `!f g. f = g` over two variables of function type came back refuted "at
f = -0.51, g = 1.39", and those are not values of `f` and `g`. The claim is false and the witness was
not a witness to it. An omitted variable has no value, so the point has no value and the answer is
`NeverAsked`.

None of `Survived`, `NeverAsked` and `Undecided` is to be read as any of the others, and neither of
the first two is to be read as any of them: `Contradictory` is a decision and `Survived` is a
report on a sample.

**The counterexample search is solved too, where the denial of the conclusion is one relation.**
Asking whether an entailment fails is asking whether the premises together with the denied
conclusion are satisfiable, which is the question one line up: over a total order the denial of
`a < b` is `b <= a`, and that step is taken here rather than in the kernel, where it would need
trichotomy and a derivation. When nothing satisfies the two together the answer is
`NoCounterexample`, which says the entailment holds over this fragment and is named apart from
`Contradictory` because the two are read in opposite directions: one says the premises are
worthless, the other says the claim is good.

An **equality as the conclusion** is not denied, because its denial is a disjunction and that is
two systems rather than one. Those go back to the sampler, which is where they were.

None of this produces a theorem, and `docs/adr/0005` says why it must not.

## What would have to be assumed

`Linarith` says whether a conclusion follows and `Refutation` says where it fails. Neither says
what is missing, and that is the question an author acts on: it is what a hostile reviewer asks.

```scala
Abduce.standard.missing("!x:real y:real. 0 < x ==> 0 < x * y")
// Gap(point = Some("x = 1.97, y = -0.215"),
//     found = Vector(0 < y),
//     vacuous = Vector(x < 0),
//     circular = Vector(0 < x * y))
```

**The proposal is untrusted and the check is not.** A candidate is a bound on a linear form the goal
writes, and each is put back to `Linarith` as a real premise; only one that makes the goal provable
is reported, so a bad guess costs a refusal. Where the bound comes from changed on 2026-09-11 and
the section on the weakest premise below is about that.

**A premise that contradicts the premises already there is not an answer**, and telling those apart
is most of what this is for. Such a premise makes every conclusion follow, so it passes the check
above while answering nothing: the first version of this proposed `x < 0` for a goal that already
assumed `0 < x`. Every surviving candidate is put to `Refutation.satisfying` with the premises it
would join, and one that leaves them unsatisfiable comes back under `vacuous`, never under `found`.
It is still reported, because a premise set one assumption away from impossible is a fact about the
argument.

**And that check answers less often than it looks.** `Refutation.satisfying` has five answers here
and only two of them decide anything: a point at which the premises hold, or a proof that no point
does. The other three say the question was not settled, which is what happens as soon as a premise
is an equality between reals the solver cannot read as a linear system. A candidate under one of
those comes back under `unchecked`:

```scala
Abduce.standard.missing("!x:real y:real. 0 < x /\\ x * y = 1 ==> 2 < x")
// Gap(point = ..., found = Vector(), vacuous = Vector(),
//     circular = Vector(...), unchecked = Vector(x < 0, ...))
```

`x < 0` is impossible under `0 < x` exactly as it is in the example above, and here nothing could
say so. Until 2026-09-11 it came back under `found`, indistinguishable from a premise the check had
passed, and on miniF2F that was 275 of the 422 candidates that close a goal. `docs/evaluation.md`
carries the measurement.

**Neither is a premise that proves the conclusion by itself**, and that one was reported as an
answer until 2026-09-10. `0 < x ==> 1 < x` came back proposing `1 < x`, and `x < 1 ==> 0 < x` came
back proposing `0 < x`, which is its own conclusion written out. Such a candidate closes the goal
and contradicts nothing, so both checks above pass it; what is wrong with it is that the premises
take no part, so what it really reports is that the argument has a hole exactly the size of its
claim. That is worth saying and is not something to assume, so it comes back under `circular`.

**A bound on a combination is in the language, since 2026-09-10**, and that is the shape a missing
premise usually has. `x + y <= 10 /\ z <= 3 ==> x + y + z <= 12` comes back with `x + y <= 9` beside
`z <= 2`, and neither implies the other. The forms are the variables and the sides of the goal's own
relations, so nothing is proposed that the goal does not write.

**The threshold is solved for and not guessed, since 2026-09-11**, and that is the difference
between proposing candidates and solving for the missing premise. The region where the premises hold
and the conclusion fails is a polyhedron; a premise `c < f` closes the goal exactly when no point of
that region has `f > c`, which is exactly when `c` is at or above the supremum of `f` there. So
there is one weakest candidate of that shape, and `Region.largest` computes it with the simplex
that was already in `Farkas`.

What that buys, measured the day before it existed:

| goal | offered then | offered now |
|---|---|---|
| `0 < x ==> 2 < x + y` | `2 < y` | `2 <= y` |
| `0 < x /\ 3 * y < 2 ==> y < x` | `2 < x` | `2 <= 3 * x` |
| `2 * x < 5 ==> x < y` | `5 < y` | `5 <= 2 * y` |
| `x < y ==> x + 1 < y + z` | `1 < z` | `1 <= z` |

Five of six goals in that measurement were offered something strictly stronger than necessary, and
the second row is the one that shows why guessing could not have got there: the threshold is two
thirds, and neither two thirds nor anything equivalent to it appears in the goal.

**Both strictnesses are offered and the check decides between them.** `f > sup` always closes;
`f >= sup` closes exactly when the supremum is not attained on the region, which is a question about
a single point and is answered by the same machinery that judges every other candidate. A threshold
of `p / q` is written `p <= q * f` and not as a fractional literal, because the numerals here are
integers and a fractional one is refused by name.

**What comes back is still the weakest of what was proposed**, and that filter still earns its keep:
two forms can both have a solved bound and neither imply the other, as `z <= 2` and `x + y <= 9` do
above. Where the region is not a polyhedron — a conclusion that is an equality, whose denial is a
disjunction and therefore two regions — the candidates are the goal's own numerals as before, and
the paragraph this replaced is what that path still does.

Two candidates that imply each other are one answer written twice, `x < 0` and `2 * x < 0`, and only
the first is kept. That was not needed while the candidates were bounds on variables, since such a
pair could not both be proposed.

**An empty answer is not "nothing is missing".** `x <= y ==> x < y` needs `~(x = y)`, which is not a
bound, and nothing is found; a goal that already follows is *refused* instead, because the two read
alike and mean opposite things.

## Deciding a quantified claim

`Ring`, `Field` and `Linarith` open a goal's leading universals and work on the body, so a statement
whose quantifiers alternate is outside all three, and `Refutation` declines a universal premise
because there is no finite domain to enumerate. `Quantified` decides one, by eliminating the
quantifiers rather than by proving anything.

```scala
Quantified.standard.decide("!x:real. ?y:real. x < y")   // Holds
Quantified.standard.decide("?y:real. !x:real. x < y")   // Fails
```

Those two are the same sentence read two ways, and telling them apart is the failure
autoformalisation is most known for. `docs/evaluation.md` reported it as the one trap of nine this
system could not separate until 2026-09-10.

**It produces no theorem, and that is the design.** This is Fourier-Motzkin elimination over
untrusted linear forms, in the same position as `Refutation` and under the same record,
`docs/adr/0005`: a model of the reals answers, nothing is certified, and no `Kernel.Thm` is built.
`Holds` is evidence of the same kind as a decided premise set, not a proof, and nothing downstream
may treat it as one. A test scans the file for the name of any inference rule to keep it that way.

**Decides:** quantifiers over the reals, nested and alternating as they like, over a body built from
`<`, `<=`, `=` between linear forms and combined with `~`, `/\`, `\/` and `==>`. Free variables are
read as universally quantified outermost, since that is what asking whether a claim holds means, so
`0 < x` with `x` free comes back `Fails` rather than answered about some `x`.
**Refuses:** a body whose linear reading keeps an atom it cannot range over, a product of two
unknowns or an inverse, by name; and an elimination that grows past its budget, since negating a
disjunction is a product over the cases and an alternating prefix over a wide body grows as the
product rather than the sum.

The two nested alternations an analysis claim is written with are decided:

```scala
Quantified.standard.decide("!x:real y:real. x < y ==> ?z:real. x < z /\\ z < y")   // Holds
Quantified.standard.decide("!e:real. 0 < e ==> ?d:real. 0 < d /\\ d < e")          // Holds
Quantified.standard.decide("?d:real. !e:real. 0 < e ==> 0 < d /\\ d < e")          // Fails
```

## Where a claim came from

A sequent carries propositions. `deaths = 53 * beds |- ...` is a formula, and what a reader wanted
was the measurement the formula came from, so `Provenance` is a table beside the proof from an
assumption to its source.

```scala
val register = Provenance.of(reals, Vector(
  "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
  "0 < beds:real" -> "ISPRA Tab. 3.1, 2026 edition"
)).toOption.get

val trail = register.trail(Linarith.standard,
  "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds").toOption.get

println(register.report(trail).toOption.get)
```

```
rests on:
  ARS 2022, table 4: deaths = 53 * beds
  ISPRA Tab. 3.1, 2026 edition: 0 < beds (weighed 7)
```

**It is outside the kernel and stays there.** A citation is not a proposition and there is nothing
to check about it; inside a theorem it would be content the trusted base carries and cannot verify.
A theorem is exactly as trustworthy with a register beside it as without.

**It reads `Linarith.support` and not the theorem's hypotheses**, because those are different
questions. A sequent's hypothesis list is an upper bound: a premise the derivation never touched
still sits in it, and attributing that would credit a measurement that took no part. The certificate
names its own support, so what comes back is the measurements the conclusion actually rests on, with
the weight each carried.

**Four groups, and the second is why this is not a map.** A premise with a source, a premise with
none, a source for a premise the proof did not need, and a source for a premise the goal does not
make. A report listing only what it could attribute would print a tidy list under a proof that also
rests on something nobody said where they got, which is an absent answer read as a negative one.

**The last two were one list until 2026-09-10, and they call for opposite things.** A citation for a
premise the goal does state, weighed zero by the certificate, says the argument assumes something it
does not need: the assumption goes, and the register was right. A citation for a proposition the
goal does not state says the register has gone stale, usually because the proposition beside it was
reworded: the register is fixed, and the argument was right. The report heads them `assumed and not
needed` and `cited and not assumed` for that reason. Telling them apart needs the goal's own
premises, which is why `attribute` takes them beside the support.

**A goal with leading quantifiers is refused, by name.** Its premises come back naming the variables
the procedure opened its quantifiers into, so every one would be uncited, and "nobody said where
these came from" is the opposite of "the question could not be asked". A claim about named
quantities is written with free variables, which is the shape this is for.

## What one claim costs, on one page

The sections above answer five different questions about a claim, and until 2026-09-10 nobody had
asked all five at once. `Cost` does, and prints the answers with their meanings kept apart.

```scala
val cost = Cost.standard
println(cost.render(cost.of("!x:real y:real. (x * y) / y = x").toOption.get).toOption.get)
```

```
Conditional: !x:real. !y:real. x * y / y = x
  1757 inferences over 8 axioms
  charges: ~(y = 0)
  believed on: !x:real. !y:real. !z:real. x * (y + z) = x * y + x * z
  believed on: !x:real. !y:real. !z:real. x * y * z = x * (y * z)
  believed on: !x:real. !y:real. !z:real. x + y + z = x + (y + z)
  believed on: !x:real. !y:real. x * y = y * x
  believed on: !x:real. x * 1 = x
  believed on: !x:real. x + -x = 0
  believed on: !x:real. x + 0 = x
  believed on: !x:real. ~(x = 0) ==> x * inv x = 1
```

Three facts about that claim, none of which a prover normally reports. It is **not true and not
false**: it holds away from zero, and the condition is on the left of the turnstile where a reader
sees it rather than in a comment. It is **believed on eight of the sixteen axioms**, and the eight
absent are the interesting half: nothing about the order and nothing about completeness takes part
in cancelling a denominator, and the inverse axiom appears exactly because one was cancelled. And
it cost **1757 inferences**, which is what a second checker will have to replay.

A claim that does not hold gets the other half of the report:

```scala
println(cost.render(cost.of("!x:real. 0 < x ==> 1 < x").toOption.get).toOption.get)
```

```
Fails: !x:real. 0 < x ==> 1 < x
  decided, not certified: settled: no non-negative combination of the hypotheses gives 1 < x, and LINARITH searched to the end of its fragment; asking again cannot change it
  fails at: x = 1
  asks for the claim back: 1 < x
  would make the premises impossible: x < 0
  would make the premises impossible: x <= 0
```

**Five outcomes, and none of them is a merge of two.** `Proved` is a theorem with nothing on its
left. `Conditional` is a theorem with a price, which is the case a procedure returning a theorem or
nothing has nowhere to put. `Holds` and `Fails` are `Quantified`'s decisions, and the report says
`decided, not certified` rather than `no proof` because the two are different facts that here
happen to agree: the label is about the outcome, and the sentence after it is about the refusal. The
second line says `settled` because LINARITH reached the end of its fragment, which is
`LogicError.Standing.Decided`; where a bound had stopped it instead, the same outcome would be
followed by the limit to raise. `Unsettled` is the rest.

**A false claim still gets abducted over.** Deciding it false is where the useful part starts, not
where the answer ends, so the point it fails at and the three kinds of candidate premise come back
beside the verdict. The three stay apart for the reason
[What would have to be assumed](#what-would-have-to-be-assumed) gives: only the first is an answer.

**An empty field means the question did not arise, not that the answer was no.** That is the same
discipline `Refutation` keeps seven outcomes for, one level up.

## Remembering: the ledger

The loop above forgets. Run it twice and it screens and certifies the same candidates twice, and
the unsettled ones, which are the ones worth reading, live until the process exits. `Ledger` is a
file of one line per question:

```scala
val ledger = Ledger.at(Paths.get("run.tsv"))
ledger.settle(Discovery.standard, left, right, Discovery.grid(Vector(left, right), 100))
// Entry("(x + 1) * (x + 1) = x^2 + 2 * x + 1", Proved, "certified by the kernel", ...)
```

Ask the same pair again and it costs a lookup rather than a certification. The file is tab
separated with a header, so `grep Open run.tsv` is how you find what is waiting for a person.

A verdict is not a record of the past. It answers whether asking again could give a different
answer: `Proved` and `Disproved` never change, `Outside` changes when the theory gains the constant
it lacked, `TooLarge` when the numeral arithmetic gets cheaper or the budget rises, `Unfinished`
right now with a higher step limit, and `Open` is the one that needs a person rather than a change.

`DecidedNotCertified` is the eighth and the name is long on purpose. It is a claim that **holds**,
settled by quantifier elimination or by a rule set decided contradictory, with no theorem behind it.
`Proved` would put a sentence in a file a person greps saying the kernel had blessed something it
never saw, which `docs/adr/0005` exists to prevent; `Open` would say nobody settled it, and somebody
did. Neither of the seven could be stretched over it, and anything shorter than the name reads as a
proof.

A reader that meets a word it does not know drops the line, so the question reads as never asked and
the work is done again. That is the safe direction and it is why adding a verdict is a change to a
**format** rather than to an enum.

## Sweeping: the generator against the ledger

`Propose` makes candidates from the library, `Novelty` says what each one cost, and `Ledger`
remembers. `Sweep` is the three composed, and it is what makes the ledger's own argument — that a
generator without a memory re-derives what it derived yesterday — a measurement rather than a claim.

```scala
val sweep = Sweep(Propose.standard, Ledger.at(Paths.get("run.tsv")))

sweep.run().lines.foreach(println)
```

```
Substituted: 64 offered, 11 remembered, 53 settled in 1442 ms, 0 refused [Proved 27, Open 17, Disproved 9]; 0.32 open per settled
Weakened: 52 offered, 9 remembered, 43 settled in 698 ms, 0 refused [Disproved 19, Open 18, Outside 5, Proved 1]; 0.42 open per settled
```

Those two lines are a **photograph** of one run against this repository's own library on 2026-09-11,
and every number in them moves when the library does. What `DocumentationSpec` runs is the example
and what it pins is the shape: a line per source, the sources named, and a rate on each. A figure
worth pinning would have to be about something that does not change every time somebody proves a
lemma.

Run it again against the same file and it settles nothing: every proposal is found and the cost is a
lookup. The last figure on each line is the one the ledger was built to make askable — how many
claims a source leaves for a person per claim it puts to the machine — and it is a figure about
where attention goes, not evidence that anything was discovered. `docs/evaluation.md` makes that
argument and nothing here answers it.

## Guessing a closed form, and proving it

The half of the discovery loop where the proposal is arithmetic on numbers and the check is a
theorem. `Family` computes a finite sum's first few values, fits the polynomial through them by
finite differences, states the claim that they agree at every `n`, and hands it to `Induct`.

```scala
Family.standard.of("\\i:num. real_of_num i * real_of_num i")
```

```
Found(!n:num. Sum (\i:num. real_of_num i * real_of_num i) n
              = real_of_num n * (real_of_num n - 1) / 2
              + real_of_num n * (real_of_num n - 1) * (real_of_num n - 2) / 3,
      degree 3, 33308 inferences)
```

Nothing was told what the answer is. What makes the claim about `n` statable at all is
`real_of_num`: `num` has no arithmetic a polynomial could be written in, and the embedding is what
turns the induction step into a ring identity in the single atom `real_of_num n`.

**The fit is a screen and the theorem is the answer.** Ten values agreeing is evidence; a family that
agrees at ten and diverges at eleven comes back as `NotCertified`, carrying the claim so that a
person can look at it. Three other things are kept apart from each other: a family with no
polynomial closed form is `NotPolynomial` and carries its values, which is not the same as a
summand whose values cannot be computed at all.

```scala
Family.standard.of("\\i:num. Power 2 i")
// NotPolynomial(0, 1, 3, 7, 15, 31, ..., sampled 10)
```

A geometric sum **has** a closed form and it is not a polynomial, so no number of differences will
find it. Saying "not a polynomial" rather than "nothing is known" is the difference between the two.

**The form is the Newton basis**, so the sum of squares arrives as `x(x-1)/2 + x(x-1)(x-2)/3` and
not as the `x(x-1)(2x-1)/6` a book prints. They are the same polynomial and `Ring` will say so; what
is not done is rearranging it here, because that would be the untrusted simplifier deciding what the
claim says.

## Finding an integer relation among numbers

The other half of the same idea, one level further from the kernel. Given real numbers known to many
digits, find the whole-number coefficients that cancel them:

```scala
Relation.among(Vector(pi, s1, s4, s5, s6), digits = 200)
// Found(Vector(1, -4, 2, 1, 1), confirmed = 196, residual = 8E-200)
```

Those five numbers are pi and `S_j = sum_k 1 / (16^k (8k + j))` for `j` of 1, 4, 5 and 6, and the
answer is the BBP formula. It is here because it is the case this method is famous for and because
it was found this way: an untrusted numeric search proposed it and something exact checked it
afterwards, which is the arrangement `docs/adr/0003` describes for this whole repository.

**The answer is a conjecture with a confidence attached, never a theorem.** `confirmed` is the digits
the agreement has left over once the size of the coefficients is paid for, because a relation among
`n` values with coefficients of size `M` is an **accident** as soon as `n log10(M)` reaches the digits
the values carry. Below `Relation.Confirmation` the outcome is `NotCredible`, which is not "there is
no relation": a relation with larger coefficients would look exactly the same, and the move is more
digits.

The ladder that makes that concrete is the minimal polynomial of `sqrt2 + sqrt3 + sqrt5`, nine values
with coefficients up to 960, at four precisions:

| digits | what comes back |
|---|---|
| 16 | `11, 3, -15, 9, 8, 7, -7, 1, 0` — noise, confirmed by 5 |
| 25 | `35, -160, 148, 11, -27, 53, 143, 74, -19` — different noise, confirmed by 5 |
| 30 | `576, 0, -960, 0, 352, 0, -40, 0, 1` — right, and confirmed by 3, so reported as not credible |
| 40 | the same, confirmed by 13 |

The thirtieth row is the one worth reading: the right answer with no evidence behind it is not a
find, and reporting it would be right by luck.

`Arbitrary` is what makes any of this possible and `docs/adr/0011` is where it came from.

## The same search, turned into a source the kernel can check

Until 2026-09-13 the paragraph here said the detector was a measuring instrument and not a source,
because a relation among real constants is not something this theory can state: it has no pi and no
infinite sums, and infinite sums want the completeness of the reals, which `docs/adr/0007` puts
after the construction. That is still true of pi. It is **not** true of an algebraic value, and
`Algebraic` is the difference.

```scala
Algebraic.standard.of(Vector(Root(2, 2), Root(2, 3), Root(2, 5)))
// Found(!x y z. x * x = 2 ==> y * y = 3 ==> z * z = 5 ==>
//         Power (x+y+z) 8 - 40 * Power (x+y+z) 6 + 352 * Power (x+y+z) 4
//           - 960 * Power (x+y+z) 2 + 576 = 0,
//       confirmed to 33 digits, 111048 inferences)
```

`sqrt2 + sqrt3 + sqrt5` is not a constant of this theory either, and it does not have to be: the
claim is about **any** three reals whose squares are 2, 3 and 5, which is an implication between
polynomial equations and needs nothing new. Nothing is defined and no axiom is added.

The proof is where the two halves meet. `Ring` decides equations true in every commutative ring, and
this claim is not one; what is one is

```
p(x + y + z) = A * (x*x - 2) + B * (y*y - 3) + C * (z*z - 5)
```

so the untrusted side reduces `p` modulo the defining equations and keeps the quotients, handing the
cofactors over as a **certificate `Ring` can check**. A wrong cofactor is a false equation and comes
back refused, which is why nothing about the reduction has to be believed.

**What the theorem says is narrower than what the search found.** The search walks the degrees upward
and reports the first that carries a credible relation, so the degree is evidence of minimality; the
theorem says only that `p` annihilates every such sum, not that `p` is minimal or irreducible.

**And a right answer from the numbers can still fail to be a theorem.** `sqrt2 + sqrt8` is `3 sqrt2`
and satisfies `x^2 - 18`, which the detector finds with digits to spare. The claim over every pair
whose squares are 2 and 8 is nevertheless false, because `(sqrt2, -2 sqrt2)` is such a pair and sums
to `-sqrt2`. The reduction leaves `2xy - 8` behind and the answer is `NotInTheIdeal`. That row is the
argument of `docs/adr/0003` run as an experiment rather than asserted: the screen agreed with itself
to fifty digits and the certification is what stopped it.

## What to do about a refusal

**Screen numerically before you attempt the proof, not after, and the reason is sharper than "it
saves time".** A refusal has exactly three possible explanations: the statement is false; the
statement is true but outside the fragment the procedure searched; or the statement is true and
inside that fragment and the proof was built wrongly. The standing described below separates the
third from the other two, and **it can never separate the first from the second**, because
`Decided` means a procedure searched to the end of its own fragment and says nothing about the
mathematics beyond it. A numeric screen taken first removes the first explanation *from outside the
system*, so the refusal that arrives is a measurement of where the procedures stop rather than a
question about whether you wrote the statement correctly. Taken afterwards it removes nothing,
because by then the refusal has already been interpreted.

Two things make it a screen rather than a coincidence, and the consumer that found this did both:
enough points that agreement is not luck, and **perturbations that bite**. A perturbation that fails
to bite means the check cannot see the error it exists to catch.

This is the same architecture as "propose numerically, certify symbolically", which
`docs/evaluation.md` argues for a search, applied to a single statement.

Every procedure above refuses, and a refusal is read in order to decide what to try next. That
decision used to be reconstructed from a message each time, and the messages are careful, but two
refusals that both print as `could not certify x + 1 = 1 + x: ...` imply opposite moves: raise a
limit, or stop believing the identity. `Remedy.of` answers the question the message was being read for, as a
value rather than as prose.

The refusal below comes from `Prove`, which is the one entry point for "prove this goal": it reads
the goal's shape, sends an equation to `Ring` and then to `Linarith` and an inequality to
`Linarith`, and reports the refusal belonging to that shape rather than whichever procedure spoke
last. On an equation both refuse it asks `Field` for the price and reports that instead, without
returning the conditional theorem under an unconditional name.

```scala
val refusal = Prove.standard("!x:real y:real. (x * y) / y = x").swap.toOption.get

println(Remedy.of(reals, refusal).message)
```

```
this is not a theorem as written; Field proves it assuming ~(y = 0): ask Field and read what it assumed, or discharge that first and nothing is owed
```

The theory is passed because a refusal carries terms and this is where a person reads them. Without
one the kernel's printer is all there is, and that one knows only equality: it writes a numeral as
the applications of `BIT0` and `BIT1` it is made of, which is correct and unreadable.
`Remedy.of(error)` is the same mapping for a caller that has no theory at hand.

An answer is mapped too, and what it comes back as is the thing to read twice:

```scala
val decided = Quantified.standard.decide("!x:real. ?y:real. x < y").toOption.get

println(Remedy.of(decided).message)
```

```
settled: the claim holds over the reals, decided and not certified; asking again cannot change it
```

**`Settled` is about this system's strength and not about the mathematics.** It says that asking
again cannot change the answer, never that the answer was yes: a refutation with a witness and a
decision over the quantifiers land there beside a proof, and the two decisions above say in the
sentence itself that nothing was certified.

**The distinction it exists to preserve** is between a question to ask differently and a defect to
report. A kernel side condition arrives as `ReportADefect`, and no rewriting of the input answers
one: a correct tactic never hands `eqMp` two sides that differ, so a caller that meets `TermsDiffer`
has found a defect in the layer between it and the kernel. Merged with `ExtendTheTheory`, which is
answered by declaring what the theory lacks, it would have a session rephrasing forever a question
that will never be accepted.

**Covers:** everything `modules/tactics` hands a caller. `TacticError` with the `LogicError` and
`KernelError` underneath it, and this module's own answers: `Refutation.Outcome`,
`Quantified.Verdict`, `CollatzScreen.Verdict`, `Discovery.Outcome` and `Ledger.Verdict`. The table
of what each ledger verdict means used to live in a comment, and this is that table where it can
fail.
**Does not cover:** `Check.Verdict`, the second reading of a proof, and not by choice.
`modules/checker` depends on the kernel and this module depends on the theories and on the algebra
system rather than on the checker, so that verdict cannot be named in the file at all. A caller
reads it where it arrives, and what a failing second reading names is a step and a rule rather than
a move: a proof that does not check is not a question to ask differently.

**The boundary is not the compiler's to keep, which is why a test keeps it.** Every mapping is a
total match over a sealed type, so a new *case* of a type already mapped stops the build; nothing
in the language notices a new *type*. That is how `Quantified` and `CollatzScreen`, which both
landed on 2026-09-10 after this mapping, reached callers carrying a verdict no arm read.
`RemedySpec` reads the sealed verdicts and outcomes out of this module's sources and holds the ones
deliberately unmapped with the reason each is out, and it fails on a reason naming something that is
no longer declared as well as on a type nobody mapped.

## What a reader is shown

A formalisation is checked by a person against the source it came from, and what that person reads
is a printed term. Printing takes part in no proof, so nothing here made the printed form and the
proved form the same object: `Show` and `Parser` are separate pieces of code, and a precedence
disagreement between them shows one formula to a reader while the kernel holds another. `Readback`
prints a term, reads the text back, and hands the text over only when what came back is the term
that went in.

```scala
val goal = reals.proposition("!x:real y:real. x < y ==> x + 1 < y + 1").toOption.get
val proved = TacticError.lift(Linarith.standard.prove(goal))
val source = "y is above x, so x plus one is below y plus one"

println(Readback.report(reals, source, goal, proved).toOption.get)
```

```
source: y is above x, so x plus one is below y plus one
formalised: !x:real. !y:real. x < y ==> x + 1 < y + 1
proved: |- !x:real. !y:real. x < y ==> x + 1 < y + 1
```

The formalisation comes before the verdict, because a verdict about a statement nobody has checked
is the thing this is against: a reader who stops after the second line has read the part that can be
wrong. A goal that was not proved keeps those two lines and gets two of its own, what refused and
the next step [`Remedy`](#what-to-do-about-a-refusal) names for it.

**The guarantee is that the text and the term are the same object under this theory's notation, and
it is nothing more.** It says nothing about whether the term says what the source said. That is the
translation problem and no round trip decides it, nor does any kernel: a formalisation can be
legible, provable, and about the wrong claim, and a proof of the wrong claim is a correct proof.
What this removes is the one failure a reader cannot catch by reading, which is being shown a
formula other than the one that was proved. So the value is negative and worth stating as such:
without it, a person checking a formalisation against an article is checking a rendering; with it,
they are checking the term. It puts the formalisation where a person can catch a wrong one, and it
decides nothing about whether the translation is right.

**It decides by trying rather than by predicting.** The plain form is printed and read back first,
and `Show.annotated` is reached for only when the plain form does not come back. The case that needs
it was found rather than reasoned about, by track P of [evaluation.md](evaluation.md) on 2026-09-07:
a free variable prints as a bare name, a bare name carries no type, and `=` is polymorphic, so
`x = y` between two reals is text this reader refuses. A bound variable never has the problem, since
its binder prints its own annotation.

**A term that does not survive is refused rather than shown with a note attached.** The text looks
right, which is the whole problem, so a caller has nothing to decide with. What comes back instead
is `NotLegible`, which `Remedy` reports as a defect in this repository rather than as something the
caller asked wrongly.

**A theorem is taken apart, and the assembly carries nothing.** `Show.show` renders a theorem as
`h1, h2 |- c`, and no reader here reads a sequent: the parser reads propositions. So each hypothesis
and the conclusion is round-tripped on its own and the line is put together afterwards. The
turnstile and the commas are punctuation.

## Extending the theory with a domain of your own

The reals are not the only thing this system can hold, and a development about something else does
not have to leave the arithmetic behind. Declare the types and constants the domain needs:

```scala
val extended = Real.standard.extended(
  Vector("agent" -> 0),
  Vector("selectivity" -> TyApp("real", Nil))
)
```

Everything from the numerals up takes what it is built on as an argument, so the whole chain
rebuilds over the result and the tactics come with it:

```scala
for {
  arithmetic <- Arithmetic.construct(extended)
  ring <- Ring.construct(arithmetic)
  order <- Order.construct(ring)
  linarith <- Linarith.construct(order)
  theorem <- linarith.prove("!x:real. selectivity < x ==> selectivity < x + 1")
} yield theorem
// Right(|- !x:real. selectivity < x ==> selectivity < x + 1)
```

**Declaring costs nothing to believe.** A constant with no definition and no axiom about it proves
exactly what its absence proves, so the theory still holds sixteen axioms and the scan that keeps
`assertAxiom` in one file still finds it there. That is what makes this the cheap half of a domain
model.

**The expensive half is not axioms either.** A model's assumptions belong on the left of the
turnstile: assume each one with `Kernel.assume`, derive under it, and the theorem that comes out
carries the assumptions it used and prints them. `Rules.disch` moves one back into the statement
when you want it there. The reason to prefer this to `assertAxiom` is not taste: an axiom is
believed by everything downstream and appears in no theorem, while a hypothesis is visible in every
theorem that rests on it, which is what lets a reader argue with the model rather than with the
system. Two things it does not give you, and both matter: the list is an upper bound rather than
the minimum needed, and nothing checks that a set of assumptions is consistent, since `h |- c`
holds vacuously when the hypotheses contradict each other. `Refutation.satisfying` is the untrusted
answer to the second.

**A declared type cannot be said to be inhabited.** `?x:agent. T` is not derivable, and asserting
it would be an axiom. That is the price of the conservativity above: as far as the theory knows,
every domain type may have exactly one element.

**No notation comes with it.** A declared constant is read and printed by its name, so `payoff a`
is an application like any other. An infix operator of one's own means a notation of one's own,
which is a larger thing than this.

### A worked argument, and what it costs

The tiering rule that governs this repository, formalised. A tier-two project has a gate; a gate
means a review or a signature; either of those is auditable.

```scala
val theory = Vector("tierTwo", "gated", "reviewed", "signed", "auditable")
  .foldLeft(Logic.standard.theory.declareTypeOperator("project", 0)) { (acc, name) =>
    acc.flatMap(_.declareConstant(name, Type.fun(TyApp("project", Nil), Type.Bool)))
  }
val domain = Logic.standard.over(theory.toOption.get).toOption.get
def reads(text: String) = Parser.proposition(domain.theory, text).toOption.get

Minimal(domain).prove(reads(
  "!p:project. (tierTwo p ==> gated p) /\\ (gated p ==> reviewed p \\/ signed p) /\\ " +
  "(reviewed p ==> auditable p) /\\ (signed p ==> auditable p) ==> (tierTwo p ==> auditable p)"))
// Right(|- …), and `Derivation.axiomsOf` of it is EMPTY
```

Three things about that, in order of how easy each is to miss.

**It costs zero axioms**, not few. The premises are on the left of the arrow where a reader can
argue with them, the connectives are definitional extensions, and nothing reaches the sixteen, the
choice operator or infinity.

**The case split is done by the machine.** *A gate means a review or a signature* is a disjunction
and the argument has to go both ways round it. That is `Minimal` on the fragment with no negation in
it, which is why this is automation on a domain and not only bookkeeping.

**The widening is not optional.** `Logic.standard` has never heard of `project`, and quantifying
over it means asking the theory for the quantifier at that type.

`DomainSpec` in `modules/theories` runs it, and runs the other arrangement beside it: the premises
assumed with `Kernel.assume` rather than written into the statement, so that what comes back names
them in its own sequent. It also holds the two boundaries. An argument needing a negation —
`~(waived r)` is the shape a real handbook rule takes — is refused by name, and `?p:project. T` is
not derivable, because as far as the theory knows there are no projects at all.

### The same argument with a negation in it, and the one call that settles it

The example above is written without a negation because until 2026-09-16 that was the price of
costing nothing: `Minimal` refuses a statement with a negation in it, and `Propositional` takes one
and charges the choice axiom. A real rule is full of negations — *a change that has not been
reviewed does not ship* — so the fragment that was free was the fragment nobody's rule is in.

`Intuitionistic` is what closed that. Dyckhoff's contraction-free calculus (G4ip), which decides
intuitionistic propositional logic with negation and falsity included, terminates on a measure
rather than on a depth bound, and builds its theorem out of the derived rules as it searches, so it
costs **no axiom at all**. It stops where intuitionistic provability stops: Peirce's law and the
excluded middle are refused here and proved by `Propositional`, at one axiom, which is the trade
made visible instead of made silently. `docs/adr/0022` is the decision.

Above it, `Domain.Built.settle` is the call a domain claim actually goes through:

```scala
val onChange = Type.fun(TyApp("change", Nil), Type.Bool)
val gate = Domain(
  name = "the release gate",
  typeOperators = Vector("change" -> 0),
  constants = Vector("TwoReviews" -> onChange, "Ships" -> onChange),
  axioms = Vector("ShipsOnlyReviewed" -> "!r:change. Ships r ==> TwoReviews r")
)
val built = Domain.build(Classical.standard.theory, Classical.standard.notation, gate).toOption.get

built.settle(Classical.standard, "!r:change. ~(TwoReviews r) ==> ~(Ships r)")
// Settled: the release gate: 1 of 1: ShipsOnlyReviewed, and no foundational axiom at all
```

Four steps, and the third is the one that makes the report worth reading. It specialises the
domain's axioms at the subjects the claim names; it decides the propositional skeleton, asking the
intuitionistic calculus first and the classical one only if that refuses; it **cuts the axioms down
to an irredundant set**, dropping each in turn and deciding again, because detaching all of them
would make `Derivation.axiomsOf` report every axiom asserted and destroy the accounting; and it
detaches, quantifies again and reports.

Four answers and not one with a flag on it. A claim that does not follow comes back as a
`Countermodel` naming the assignment, which refutes it **as a schema over uninterpreted atoms** and
never says the claim is false. A claim reaching a constant of the foundation rather than of the
domain — arithmetic, an order, a numeral — comes back `Refused` naming the constant **when the
caller has named no bridge**, because an atom with no meaning is not an approximation of *at most
three attempts*. What lifts that is `docs/adr/0024`: a theorem the caller hands over, specialised at
the claim's own foundation-typed subterms, which stay opaque throughout, so what it costs is
reported in the foundational column rather than absorbed. `Bridging` is the same route with the
theorem found instead of named, one candidate at a time out of the library's lemmas about the
constants the claim reaches, reporting which of them carried it; `docs/adr/0027` is that
decision, and composing any of this with `Linarith` is still a different piece of work.

A domain that keeps a **type** of its own is the case neither of those covers, and what stops it is
not a refusal but the parser: `NUM_LT c 3` at `c:cost` is a type error, so there is no verdict to
lift. `docs/adr/0028` is the answer — an interpretation handed to `Domain.build`, which sends the
domain's type to a foundation type and, where the caller wants it, sends a domain constant to a
**definition** rather than a declaration. Neither costs an axiom, and what the report gains is
`Domain.Spending.defined`: the interpreted names the conclusion rests on, because a claim resting on
a translation rests on something the axiom columns will never mention. And a claim
settled only after the free route ran out of net comes back `CutShort` rather than `Settled`: the
theorem and the price are the same, and what is added is that the `SELECT` may be the search's
rather than the claim's, which `docs/adr/0026`
decides and `DomainTheorySpec` measures at the chain length where it happens.
`DomainTheorySpec` runs all four.

### A whole argument on one page

`Cost` answers five questions about one claim and `Provenance` names the sources behind one proof.
A document is neither: it is a dozen claims leaning on each other and on one register of
measurements, and there is a question that only exists at that size.

```scala
val register = Provenance.of(extended, Vector(
  "0 < rate"          -> "ISPRA Tab. 3.1",
  "load <= 60 * rate" -> "ARS 2022, table 4",
  "cap = 100 * rate"  -> "Decreto 152/2006 art. 101",
  "0 < load"          -> "ARS 2022, table 7",
  "load < cap"        -> "Decreto 152/2006 art. 99")).toOption.get

val argument = Argument(cost, linarith, register, Real.standard.theory.axioms.toSet)

argument.render(argument.read(Vector(
  "0 < rate /\\ load <= 60 * rate /\\ cap = 100 * rate ==> load < cap",
  "0 < rate /\\ cap = 100 * rate ==> 0 < cap",
  "0 < rate /\\ 0 < load ==> 0 < rate + rate")).toOption.get)
```

```
3 claims, 3 proved, 0 decided, 0 open; 0 axioms of the domain, 13 foundational; 1 idle citation and 1 stale citation
Proved: 0 < rate /\ load <= 60 * rate /\ cap = 100 * rate ==> load < cap
  12446 inferences over 13 axioms
  weighed 40, from ISPRA Tab. 3.1: 0 < rate
  weighed 1, from ARS 2022, table 4: load <= 60 * rate
  weighed -1, from Decreto 152/2006 art. 101: cap = 100 * rate
Proved: 0 < rate /\ cap = 100 * rate ==> 0 < cap
  9157 inferences over 13 axioms
  weighed 100, from ISPRA Tab. 3.1: 0 < rate
  weighed -1, from Decreto 152/2006 art. 101: cap = 100 * rate
Proved: 0 < rate /\ 0 < load ==> 0 < rate + rate
  7165 inferences over 13 axioms
  weighed 2, from ISPRA Tab. 3.1: 0 < rate
  believed on: ...thirteen axioms of the ordered field...
  assumed and never weighed: 0 < load (ARS 2022, table 7)
  cited and never assumed: load < cap (Decreto 152/2006 art. 99)
```

**The question that only exists here is whether a citation is stale.** Asked of one claim the answer
is nearly always yes and nearly always wrong: a register of five citations and a claim that weighs
two leaves three looking unused, when two of them are used by the next claim. So the three buckets
are computed over the argument. `load <= 60 * rate` is used, and `Provenance.trail` on the third
claim alone calls it stale, correctly, because that claim does not state it. `0 < load` is **idle**:
a claim states it and no certificate anywhere weighed it, so the argument assumes something it does
not need and the register is right. `load < cap` is **stale**: no claim states it at all, so the
register is out of date and the argument is right. The two are fixed in different files, which is
why they are two lists.

**The axioms come in two heaps.** What this repository asks everybody to believe, and what this
document asked for on top. The second is the part a reader of the document can argue with, and here
it is empty: three declared constants cost nothing, every assumption is on the left of a turnstile,
and the thirteen are the ordered field. The list is printed once for the document and the **count**
stays on every line, because a claim that reached three axioms and one that reached thirteen are not
the same claim.

**A conclusion with no linear certificate is still costed.** A ring identity has no Farkas
multipliers to report, and leaving the line blank would hide the outcome, the price and the axioms,
which the tactics can all still answer for. `Line.whyNoPremises` carries the refusal beside it.

**Nothing here checks that the premises can all hold at once.** `h1..hn |- c` is vacuously true when
the premises contradict each other, so an argument with inconsistent assumptions proves everything.
`Refutation.satisfying` is the untrusted answer and it is a question about the assumptions rather
than about the conclusions; this page does not ask it, and a page that looked complete without it
would be the more dangerous artifact.

## Adding a lemma of your own

Prove it; do not assert it. `Kernel.assertAxiom` exists and is named so that it reads as what it is
at the call site, and every axiom added that way enlarges what has to be believed.

The pattern used throughout `Arithmetic` is: state the lemma as text, prove it by normalising both
sides, and close it over its free variables so it becomes a rewrite rule.

```scala
val statement = reals.proposition("x:real * (y:real + 1) = x * y + x")
val proved = statement.flatMap(Ring.standard.prove)
```

If a lemma cannot be proved by a tactic, it is derived by hand, and `Arithmetic` contains a dozen
worked examples of what that looks like, including the one place where the derivation reads like a
proof on paper: `x * 0 = 0` is not an axiom of a field and needs the additive inverse and a
cancellation.

## What is missing, and the order to add it

1. **A type definition mechanism in the kernel.** Done on 2026-09-10 as `Kernel.defineType`, and
   `docs/adr/0006` is the record. It cost 107 lines of the trusted base and no axiom.
2. **The natural numbers, and induction.** Done on 2026-09-10. `Natural` in `modules/theories`
   declares a type `ind`, asserts infinity over it, names a successor and a point outside its image
   with the choice operator, and carves `num` out as the smallest inductive subset, with zero and a
   successor defined on it. Induction is **derived**:

   ```
   |- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> !n. P n
   ```

   It is the definition of `NUM_REP` read back rather than anything new to believe, and its
   derivation reaches no axiom at all, which `RecursionSpec` measures. It runs through the
   inductive predicate `\x. NUM_REP x /\ P (mk_num x)`: it holds of `IND_0`, it is closed under
   `IND_SUC`, so every representative satisfies it, and the bijection carries that to every number.

   **Recursion landed the same day**, so a function on the naturals is defined rather than assumed:

   ```
   |- !e f. ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)
   ```

   It is where the axiom of infinity is finally spent. Uniqueness of the recursive graph needs
   `SUC n` never to be `ZERO` and `SUC` to be injective, and nothing below it does: the type,
   induction and the case split reach no axiom at all.

   **Finite sums are built on it**, in `Series`: `Sum f ZERO = 0`, `Sum f (SUC n) = Sum f n + f n`,
   and then linearity, the telescoping sum and summation by parts, each one induction whose step is
   a rewrite and a ring identity. `Ring` has never heard of `Sum` and does not need to: an
   application it cannot take apart is an atom, which is the right reading of a sum whose length is
   a variable.

   **`Chain.standard` assembles the whole of it in the order that works**, which is the naturals
   first and the reals over them. The order is not free: a tactic is built over a `RealTheory`, so
   the other way round gives a signature with both types and tactics that read half of it. It is not
   there for speed, which was measured and found to be about 110 ms once per process.

   **`Induct` is the driver**, since the shape never varies: strip the quantifiers that are not the
   number, instantiate induction at the predicate, rewrite each half with the recurrences and, in
   the step, with the induction hypothesis, and hand what is left to `Ring`. Two things go wrong
   silently without it, and both are fixed once: using a fresh variable instead of the one the
   induction binds, and the side condition on `gen`.

   Its default step wants **the induction hypothesis to be usable as a rewrite**, so its left side
   has to be a subterm of the step goal. `!n. Sum f n = Power 2 n - 1` has that shape and
   `!n. Sum f n + 1 = Power 2 n` does not, and they are the same statement; `Induct.proveBy` hands
   the two halves to the caller for that case. They arrive as functions rather than as a list of
   waypoints because a caller cannot name the variable the step is about: the driver opens the
   quantifier and the variable is fresh.

   **`SUM_CONGRUENCE` is narrower than it looks**, and the measurement that says so is worth more
   than the lemma. The rewriter goes **into** the lambda `Sum` binds, so `Sum (\i. ff i) n` and
   `Sum (\i. 2 * ff i) n` are rewritten where they stand and need nothing. What does not move is a
   **bare symbol**, `Sum ff n`, which is what a development that quantifies over its summand has.
   There is no redex to go into, so until 2026-09-10 a congruence lemma was the only route:

   ```
   |- !f g. (!i. f i = g i) ==> !n. Sum f n = Sum g n
   ```

   **Eta is what removed the reason for it.** `Classical.ext` takes `G ⊢ !x. f x = g x` to
   `G ⊢ f = g`, and congruence on the equation carries it into any binder at all, in three steps
   rather than an induction. The lemma is still proved and still exported, because a caller holding
   the pointwise hypothesis should not have to know which of the two routes is cheaper. What changed
   is that the next binding operator does not need one of its own: the products, integrals and
   maxima this paragraph used to promise a lemma each are covered by the rule.

   That is the whole justification for the second axiom, and it is the one `docs/adr/0007` requires:
   an axiom arrives in the commit whose derivation needs it and never in advance. `SUM_CONGRUENCE`
   is a derivation in this repository that was paying for its absence. **What has been delivered is
   the rule and not yet the saving**, and `docs/adr/0009` records the gap rather than closing it:
   `Series.congruent` still reaches `SUM_CONGRUENCE` by induction, so the claim above is an argument
   about what `ext` can do and not a measurement of a lemma that got shorter. `Prod` landed the same
   day and did want `PROD_CONGRUENCE`, which is the prediction holding for the last time.

   Sequences and limits landed on 2026-09-15, in `Limit`, and item 4 below is what they were
   for.
3. **The classical axioms, both of them, landed on 2026-09-10.** `Classical.scala` asserts two
   statements and both are HOL Light's, transcribed from `class.ml`:

   ```
   SELECT : !P x. P x ==> P (select P)
   ETA    : !t:'a->'b. (\x. t x) = t
   ```

   `SELECT` is a constant that picks an inhabitant out of any predicate that has one and is
   constrained nowhere else, exactly as the field axioms leave `inv 0` alone. It was spent on
   **naming a witness**, which is what `Kernel.defineType` cannot do without: a type is carved out
   by a closed predicate, and a witness obtained by eliminating an existential is a variable, so the
   successor function the axiom of infinity says exists had to be named before `num` could be carved
   with it. Upstream spells the constant `@`; this lexer cannot read that character, so it is
   `select`, and the divergence is a spelling and nothing more.

   `ETA` is the second, and it was asserted for `SUM_CONGRUENCE` rather than for the excluded
   middle. The paragraph above under item 2 is the whole of what it bought and what it did not, and
   [the subsection on the excluded middle](#the-excluded-middle-is-derived-and-it-cost-no-axiom-of-its-own)
   is why the second of those was free.

   Both live in an extension beside `Logic.standard` rather than in it, so that a development can be
   asked which of its results need them. `Logic.standard` holds no axiom and proves exactly what
   the empty theory proves, `Real.standard` holds the sixteen and neither of these two, and a
   development over the naturals holds these two and infinity, which is three and is
   `NaturalSpec`'s measurement rather than this document's. A chain holding both the reals and the
   naturals holds nineteen, and that figure is `ChainSpec`'s.

   **What is still not asserted, anywhere.** The third of HOL Light's three axioms is infinity, and
   it is not in the logic: it belongs with the naturals and `Natural.scala` has it. Nothing else
   about the formalism is assumed. In particular `bool` having exactly two elements is not:
   upstream's `BOOL_CASES_AX`, `!t. t = T \/ t = F`, is reachable from `cases` and is a theorem here
   rather than an axiom, though nothing has yet needed it enough for it to be derived and pinned.
   And the reals are still axiomatised: the sixteen are what `docs/adr/0007` turns into theorems at
   the end of the construction, and that work has not started.
4. **Trigonometric, exponential and logarithmic functions**, defined rather than assumed. The
   definitions landed on 2026-09-15 and nothing beyond them did. `Limit` declares `converges` and
   `lim`, both definitions: the first is the epsilon-N statement written out, the second is choice
   applied to it and is pinned by `CONVERGES_UNIQUE` wherever the sequence converges.
   `Transcendental` declares `exp`, `sin`, `cos` and `ln`, each its power series through that limit,
   and `docs/adr/0017` is the decision that they are definitions rather than four new axioms.

   **What is proved of them is the value of each at zero**, and that is reachable only because a
   series at zero stops moving after its first term: `CONVERGES_CONSTANT` with
   `CONVERGES_EVENTUALLY` settles a sequence that is eventually constant, and no convergence
   theorem is involved anywhere.

   **The monotone convergence theorem landed the same day**, `MONOTONE_CONVERGES`: increasing and
   bounded above gives convergent, by the least upper bound, and it is where `COMPLETENESS` is
   spent a second time. It is the first thing in this repository that obtains a limit rather than
   assuming one, and what it cost in front of it was a rule of the logic rather than a lemma of the
   analysis: `Classical.NOT_FORALL`, since "otherwise the supremum would not be least" is a negated
   universal turned into a witness.

   **The comparison test landed on 2026-09-16 and it did not buy what this paragraph promised.**
   `SUM_COMPARISON` is the sentence that was written here: a series with non-negative terms under
   one whose partial sums are bounded is a monotone bounded sequence, so the theorem above finishes
   it. What came with its first consumer is `CONVERGES_LE` and `CONVERGES_GE`, a bound respected
   from an index on being a bound the limit respects, because the test hands back an existential
   and a caller wanting to know where the limit sits could not say so.

   `exp 1 > 2` did **not** become a theorem with it, and the difference between the prediction and
   the outcome is the piece worth carrying: what was missing was not the test but a dominating
   series for the exponential. `1 / i!` under `2 * (1/2)^i` wants `2^i <= 2 * i!` and an order fact
   about a quotient. The second landed on 2026-09-18 as `Order.INV_ANTITONE` with `LE_MUL_BOTH`
   under it, and **the first on 2026-09-20 as `Coding.NUM_POW_LE_FACT`**, which is not the two-base
   induction it looks like: the shifted claim goes through the ordinary induction and `NUM_CASES`
   joins it to the value at zero. With both, `Transcendental.EXP_ONE_ABOVE_TWO` is `2 < exp 1`, and
   the whole distance from the comparison test to that theorem was arithmetic on `num` rather than
   anything about limits. The geometric series at one half needed neither and `LimitSpec` had
   obtained it with its limit between zero and two, which is the model the exponential's follows.

   **What came after that** is the addition theorem through the Cauchy product, on 2026-09-21, and
   on 2026-09-24 the Pythagorean identity, `SIN_COS_SQUARED`, through a second pair of Cauchy
   products at the two alternating series. The same day `Continuity` defined continuity at a point
   and proved the intermediate value theorem from `COMPLETENESS`, and `Logarithm` spent it on the
   exponential: continuous everywhere, onto the positive reals, and `ln` its inverse, with
   `EXP_LN`, `LN_EXP`, `LN_ONE` and `LN_MUL`. On 2026-09-25 whether a series converges became something the
   system **decides** rather than something a reader assembles: `Convergence`, reached through
   `Prove.Address.Series`, answers in both directions over the geometric, exponential, sine and
   cosine summands, and `docs/adr/0041` says why it reads closed forms instead of applying the
   ratio test it also publishes.
5. **A proof for what `Quantified` decides.** Since 2026-09-10 a quantified linear claim is
   decided, and it is decided rather than proved: the elimination runs on untrusted forms and no
   theorem comes back. Making it produce one wants the density and the unboundedness of the order
   as derived lemmas, `a < b ==> ?c. a < c /\ c < b` and `?c. a < c`, and then an elimination that
   builds a theorem at each step instead of a form. That is the first place where something this
   system decides could become something it proves.
6. **More of what `Linarith` cannot see.** The linear fragment is decided since 2026-09-05, and
   the products of the hypotheses reach past it since 2026-09-09. Three things this list named as
   the limit went on 2026-09-10 and none of them was a missing idea: a goal that wrote a product
   over a difference instead of distributing it, `0 < p /\ d < q ==> 0 < p * (q - d)`, was read as
   an atom nothing else mentioned; the negation of the goal took no part in the products, which is
   what put `0 < x * y /\ 0 < x ==> 0 < y` out of reach; and an equality took part in none either.
   Degree three fell with a second round of products, run only when the goal names an atom the
   pairs did not reach, so `0 < x /\ 0 < y /\ 0 < z ==> 0 < x * y * z` is proved. What came next
   was not a fourth round: the two corpus goals that asked for more have **no hypotheses**, so the
   pool the products are built from is empty for them at every degree, and since 2026-09-18 both
   are settled by one completed square instead, which `docs/adr/0032` decides, saying why a
   parametric degree was rejected. What is left is a general sum-of-squares certificate, a search
   outside the trusted boundary with its answer checked inside, which is where the inequalities
   `docs/adr/0029` calls genuinely hard would be spent. The refusal names the atom, how many
   unknowns it multiplies, and whether what stopped it was the degree or an empty pool, rather
   than telling an author to restate as a combination of hypotheses that no combination reaches.

Each step unlocks the next and none of them is research. The mathematics beyond them is.
