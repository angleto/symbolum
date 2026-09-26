# Where it stands

**EXCERPT — for anyone scanning the index:**
What the proof side reaches today, development by development: what each one derives, what it
spends, what it declares, and what is not written between them, stated as gaps rather than as
plans. The order in which the gaps get closed is kept in the task tracker, not here. The list of
every lemma is [lemmas.md](lemmas.md) and the showcase is [theorems.md](theorems.md). Until
2026-09-25 this text was a section of `CLAUDE.md`, and where it says "this file" about its own
past it means that section.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

The mathematics the proof side can reach is still small. The type-definition rule landed on
2026-09-10 and the naturals with it: `num` is a defined type in
`modules/theories/.../Natural.scala`, carved out of an infinite one as the smallest inductive
subset, with zero, a successor, and **induction, Peano's other axioms and the recursion theorem all
derived** rather than assumed. `Series` builds finite sums on the recursion theorem, with linearity,
the telescoping sum and summation by parts. `Peano` adds the arithmetic, the two orders, the
embedding into the reals, and since 2026-09-11 the predecessor and a truncated subtraction, which is
the only subtraction `num` can have and which the file says of itself in its first paragraph.

**The sixteenth axiom of the reals is read by exactly one thing, and it arrived on 2026-09-13.**
`COMPLETENESS` had never been used: fifteen of the sixteen were worked and the one that separates an
ordered field from the reals was not. `Peano.NUM_ARCHIMEDES` is what spends it, and it has to be
proved rather than assumed because an ordered field need not be Archimedean. What it bought
immediately is `NUM_FLOOR` and `NUM_CEIL`, named by choice and costing no axiom. Both carry `0 <= x`
as a written hypothesis rather than a hidden one: `num` has no negative numbers, so a floor that
answered below zero would be right above it and silently wrong under it, and the version with no
condition at all wants the integers.

**`defineType` is called by hand for the types the chain is built from, and by builders that
carve a type from a description.** By hand: `num`, then `prod` in `Product.scala`, carved out of
`'a -> 'b -> bool` the way `pair.ml` does it, then `word` in `Word.scala`, a length and a padded
function held together in a pair; the second and third exist because lists, matrices and index
types were all one missing primitive, and it was the pair. This paragraph counted those uses
until 2026-09-25 and said three while `Quotient` was already the fourth, which is why it counts
nothing now: `git grep -n "defineType(" -- 'modules/*/src/main/*.scala'` is the census, and its
first line is the declaration. The file part of that pathspec is not decoration: without it the
same command answers nothing, which reads exactly like a repository with no call site.

The builders are `Quotient`, the classes of an equivalence relation, whose first consumer is
`int`, and since 2026-09-25 **`Datatype`, an inductive type from a list of its constructors**, with
its induction principle, case analysis, injectivity, distinctness and recursion theorem all derived
and `Datatype.defineRecursive` to name a function by structural recursion. Every such type lives in
one universe of labelled trees, `word(num) -> L -> bool`, and `docs/adr/0042` is the construction.
The one discipline it asks of anyone editing it is that the node of the universe is a **term** and
not a constant, so nothing in the builder may normalise a term holding one: every reduction there
is at the root. Induction and case analysis spend no axiom; injectivity, distinctness and recursion
spend choice, eta and infinity, which the chain already holds. Its consumer is `Syntax`, the terms of
Peano arithmetic as a type `pterm` with the five constructors `Language` numbers, `PSUBST` by
structural recursion, and `PSUBST_SELF` proved by induction; it sits beside the chain by decision,
since in it every `PVAR` would sit next to a `NUM_CODE`. So a syntax can be a type here now, and
the object level is still numbers for the reason `docs/adr/0014` gives: the embedded theory
quantifies over codes. That the code of `PSUBST` of a term is `NUM_SUBST_TERM` of its code is
statable now and not proved.

**Recursion along a measure is `WellFounded`, since 2026-09-25**, and it is the third recursion
theorem after `Recursion` on the successor and `Descent` on a code:
`!m st. (!f g x. (!y. m y < m x ==> f y = g y) ==> st f x = st g x) ==> ?f. !x. f x = st f x`. The
hypothesis is **admissibility**, the caller's to discharge because it is a fact about a step, and
`docs/adr/0043` is why it is a measure into `num` and not an arbitrary relation. It costs choice and
infinity and not eta. `EuclidAlgorithm` spends it, beside the chain, as `NUM_EUCLID_GCD` — not
`NUM_EUCLID`, which is Euclid's lemma — whose equations compute `NUM_EUCLID_GCD 4 6 = 2`, and since
the same day `NUM_EUCLID_GCD_IS_GCD` says that value is `NUM_GCD` off both zero, so `NUM_GCD 4 6 = 2` is
a theorem reached by computing. `NUM_EUCLID_DIV` is the second thing it defines, the quotient by
repeated subtraction, and `NUM_EUCLID_DIV_IS_DIV` ties it to `NUM_DIV` off a zero divisor.

`Rotation` needs two others at once: `Word` for the type it rebuilds and `Modular` for the
`NUM_MOD` inside its own definition. That is why it is not in `Word.scala`: `Word.standard` is built
below `Modular` and cannot state a rotation at all, so a rotation living there would build in the
chain and refuse beside it.

It was the last link and `Chain.widest` until 2026-09-13. **This sentence has now named the wrong
development twice**: first for four hours, then for a day, while it said `Magnitude` and the field
said `Coding`. So it no longer names one. Which development is last changes whenever a link is
added, five times in two days, and `Chain.widest` is the one place worth reading for it. What a
wrong name costs is what the first correction recorded: a reader of it would have gone looking for
`max` in `Rotation`'s signature.

**Concatenating two words is `Concatenation`, a link since 2026-09-16, and it is the operation the
type did not have.** `WORD_CONCAT`, the empty word and the one-letter word, and from those three the
prefix, the suffix and the factor, each **defined by the concatenation** rather than beside it,
which is what makes `WORD_FACTOR_LENGTH` one lemma instead of three. Six constants, no axiom, and
the facts `docs/lemmas.md` lists under `Concatenation`, which include associativity, both units, and
an induction that extends a word **on the right** rather than on its length. That sentence carried a
count of fifteen until 2026-09-17 and the section held seventeen by then, `WORD_CONCAT_TALLY` and
`WORD_LENGTH_ZERO` having landed after it: a count beside a generated document is the copy that
drifts, and the document is regenerated by a command `LibrarySpec` names when it goes red. Before it, `?x y. w = x u y` was not a sentence this
repository could write, so of a factor nothing could be said, not even wrongly.

It is **not** a development of its own for `Rotation`'s reason, and the difference is the thing to
carry: `NUM_MOD` really is outside `Word.standard`'s signature, and `NUM_ADD`, `NUM_SUB`, `NUM_LT`
and `COND` are all inside it, so this could have gone in `Word.scala` and would have built. What
decided it is size and subject, and `ConcatenationSpec` asserts that the constants this link adds to
the theory below it are exactly those six, rather than leaving the claim in prose. This said four
until 2026-09-17, which is the same sentence naming the same spec and disagreeing with the line
above it.

What it cost in front of it was three lemmas about `num` that nobody had needed:
`Peano.NUM_ADD_LT_CANCEL`, `NUM_LE_OF_NOT_LT` and `NUM_SUB_SUB`. The last is the one to know about,
because it is what decides the third case of associativity: an index past both of the first two
blocks is `w`'s at `i - (|u| + |v|)` read one way and at `(i - |u|) - |v|` read the other, and
nothing said those were the same number. That they are, with **no** side condition, is a property of
truncated subtraction rather than a coincidence.

**And the absence of a constant is not a parse error here, which is the trap this landed on.**
`ConcatenationSpec` first asserted that the statement it exists for is *refused* by the signature one
link down. It is not: an unknown letter-initial name parses as a **free variable**, so the same text
against `Transcendental` is well-typed and is a claim about an arbitrary function spelled
`WORD_CONCAT`. That is the trap the `Chain.peano` note records for `NUM_LE ZERO n` and `ChainSpec`
records for `zork`, met a third time. The question that separates the two signatures is whether the
name is a **constant** of the theory, and the spec asks that one now.

**A list is an orientation on `word` rather than a type, and `Listing` is that link since
2026-09-23.** The card asking for it wanted `list('a)` carved with `defineType` beside `num`,
`prod`, `word` and `int`, on the stated ground that `word` is not polymorphic. It is: the arity of a
carved type is read off the free type variables of the predicate, and `Word`'s is
`\p:prod(num,num->'a). ...`, so `word('a)` is a type operator of arity one and a word over any type
is a word. A second carve would be **from the same predicate**, so the carrier would be isomorphic
to one that exists and would inherit none of its seventeen facts. `docs/adr/0038` is the decision.

What was missing is one principle and not a type. `Concatenation.WORD_INDUCTION` extends a word **on
the right**, and a definition by recursion on a sequence descends from the **left**. So `LIST_CONS x
w` is `WORD_CONCAT (WORD_SINGLETON x) w` under a name, `LIST_HEAD` and `LIST_TAIL` are its two
inverses, and `LIST_INDUCT` is cons-induction, derived the way the mirror is: `Natural.Induction`
over `\n. !w. WORD_LENGTH w = n ==> P w`, with `LIST_CASES` supplying the decomposition. Three
definitions, no axiom, **no type**, and `ListingSpec` asserts the last of those as a difference of
type operators rather than leaving it in prose.

**The empty list is `WORD_EMPTY` and has no second name**, which is the whole of what a link rather
than a duplicate means here: a reader who has a word has a list, `WORD_CONCAT` **is** append, and
there is no coercion at any boundary. The distinctness and injectivity a carved free algebra gets
from its tags are theorems instead, `LIST_CONS_NOT_EMPTY` off the lengths and `LIST_CONS_INJECTIVE`
off the head and the tail.

**`LIST_RECURSION` is what a *definition* needs, and `LIST_INDUCT` is not it.** Induction proves a
property of every list and produces no function, so until the recursion theorem landed the interface
could be used in a proof and not in a definition. `word('a)` is a defined type and the only recursion
principle it has is the one it was carved with, which is `num`'s, so the function is built at one
remove: `Recursion.theorem` at the result type `word('a) -> 'b` gives an `F : num -> word('a) -> 'b`
and what the theorem asserts is `\w. F (WORD_LENGTH w) w`. **No induction happens in it**, which is
worth saying because the statement looks like it should need one: the empty word's length is `ZERO`
and a cons's is `SUC (WORD_LENGTH w)`, so each of `F`'s own two equations fires once and
`LIST_HEAD_CONS` and `LIST_TAIL_CONS` read the arguments back. That step is why `LIST_HEAD` and
`LIST_TAIL` are constants here rather than terms built inside a proof: it has to name them.
`LIST_RECURSION_UNIQUE` is beside it and not a `?!`, this logic having no unique-existence
quantifier, which is how `Recursion.Statement` on `num` is written for the same reason.

**The consumer is `Folding`, a link of the same day, and it is what makes that theorem a fact this
repository spends rather than one it holds.** `LIST_FOLD g a (LIST_CONS x w)` is
`g x (LIST_FOLD g a w)`: one constant, no axiom, no type, defined by the recursion and not provable
into existence without it. Its step is handed the letter and the value so far and **not** the tail,
which `docs/adr/0039` decides and which is not a simplification: `LIST_FOLD_CONCAT` is **false** for
a step that can read the tail, because at `LIST_CONS x u` one side's tail is `WORD_CONCAT u v` and
the other's is `u`. A caller wanting the general form has `LIST_RECURSION` itself.

What the consumer measures is the difference the orientation buys, against a lemma this repository
already holds. `Concatenation.WORD_CONCAT_TALLY` splits an aggregate over a word by **position**, so
the right half's letters are re-read `NUM_ADD (WORD_LENGTH u) i` further along and every consumer
carries that correction whether it weighs by position or not; `LIST_FOLD_CONCAT` carries none, and
`FoldingSpec` asserts that by walking the constants each of the two statements names rather than
leaving it in prose. The other half of the same sentence is the cost: a fold cannot express a
measure that weighs a letter by where it sits, `S2_PHI` is the consumer that wants one, and the
tally is not superseded.

**A development that existed before the lists writes with them since 2026-09-25, and it is
`Collatz`.** A new development was not what the card that asked for lists wanted, and Angelo held
it to that. `S2_TAILFREE` and `S2_HEADFREE` are folds of conjunctions now, and their split over a
concatenation is `LIST_FOLD_EVERY_CONCAT` at the marker, where it was 150 lines of index
arithmetic. Nothing else in the file moved, because `LIST_FOLD_EVERY` is the bridge to the reading
by position and the old definitional equation is **derived** from it and handed to the proofs that
ran on it. What it cost is eta on six of its facts, every fact about a fold resting on the carved
type's extensionality; the count and the decision are in `docs/adr/0039`, and so is why `Collatz`
and no other candidate: `Forward` and `Rotation` sit below `Listing` in the chain, and `Collatz`
sits beside it and can be built over `Folding`.

**And what could have gone vacuous is guarded by spending both theorems at once.** An existential
nobody discharges and an implication nobody detaches read exactly like facts. `ListingSpec` takes
the witness at the step `\x. \w. \r. SUC r` and the start `ZERO`, observes that `WORD_LENGTH`
satisfies those two equations already — `WORD_EMPTY_LENGTH` is the first and `LIST_CONS_LENGTH` is
the second — and closes with the uniqueness. What comes out is that the function the recursion
produced **is** `WORD_LENGTH`, owing nothing, which is a theorem this repository proved long before
either principle existed.

Number theory on `num` is `Modular`, a link in the chain since 2026-09-12: divisibility with the
antisymmetry that is false over a field, congruences with their compatibility with addition and
multiplication, division with remainder in both halves, `NUM_DIV` and `NUM_MOD` as functions that
denote and are total, the greatest common divisor, Bezout, and Euclid's lemma with a definition of
prime. `Bounded` discharges `!i. i < k ==> P i` at a concrete bound by proving the instances and
assembling them, and was the one development that sat beside the chain's extension order rather than
in it, because it declares nothing. It is one of three now: `Primes` and `Deduction` joined it on
2026-09-14.

**`Primes` holds theorems about the primes that are results rather than infrastructure**, and
`docs/lemmas.md` is where they are counted; this paragraph said "today that is two" while the file
held six, a count beside a generated document being the copy that drifts. The first two are Euclid's, `!n. ?p. NUM_PRIME p /\ NUM_LT n p`, which is what "there are infinitely many
primes" says in a logic with no notion of an infinite set. And `NUM_SQUARE_NOT_DOUBLE`, that no
square is twice a square at a positive denominator, which is the arithmetic content of the
irrationality of the square root of two and is **not** that sentence. The sentence is
`Root.SQRT_TWO_IRRATIONAL`, since 2026-09-24: `sqrt 2` is not a ratio of naturals, proved by
clearing the ratio, squaring, and carrying the equation back across `real_of_num`, where this fact
refuses it. It lives in `Root` because `Primes` is built before `sqrt` exists.
`PrimesSpec` asserts that its hypothesis cannot be dropped, by proving the equation at zero. It is not in `Modular` because of one
constant: the proof runs through `n! + 1` and the factorial is defined in `Coding`, which is built
**over** `Modular`. Putting it in `Coding` instead would have made that file's own first sentence
false, since `Coding` says it is the bottom of the Goedel numbering and this is not that.

**What proving it cost was one missing lemma, and that is the whole reason to prove such things
here.** `NUM_PRIME_FACTOR`, that every number above one **has** a prime factor, did not exist.
`NUM_PRIME_DIVISOR` is a letter away and says the opposite direction, that a prime's divisors are
one and itself, which is the definition unfolded. Nothing had ever needed the existence, so nothing
had noticed. It is in `Modular` beside the name it is confused with, and the route is the **least**
divisor above one rather than the textbook induction: the least one is prime for free, and the
induction would want a negation pushed through a universal quantifier, which this logic had no law
for until `Classical.NOT_FORALL` landed on 2026-09-15; the route is unchanged, since the least
divisor asks for nothing beyond `NUM_LEAST`.

**Fermat's little theorem is `NUM_FERMAT`, since 2026-09-25, and the binomial theorem on `num` came
with it.** `NUM_CONG p (NUM_POW a p) a` at every prime `p` and every `a`, in the congruence form that
needs no division, by induction on `a` over `NUM_FRESHMAN`, that `(a + 1)^p` is `a^p + 1` modulo
`p`. What that rests on is `NUM_BINOMIAL` at `x + 1` and `NUM_PRIME_DIVIDES_CHOOSE`, that `p`
divides every middle coefficient: `Coding.NUM_CHOOSE_FACTORIAL` at `p = k + (p - k)` puts `p!` on
one side, `p` divides it, and Euclid's lemma applied twice meets `NUM_PRIME_NOT_DIVIDES_FACT` at
both factorials on the other.

**The binomial theorem is proved on `num` by Pascal's rule and is not carried across from
`Series.POWER_BINOMIAL`**, and the reason is a measurement: the transported version worked and
rested on seventeen axioms, the reals' sixteen among them, which
`NothingOverNumRestsOnTheRealsSpec` refuses for a fact about the naturals. The native one costs the
naturals' two. `Freshman.scala` is the derivation and is not a development; `FermatSpec` detaches
the theorem at two, asserts the route, and refutes the statement with its hypothesis dropped at
`p = 4, a = 2`, where `2^4` leaves nought on division by four.

**Euler's theorem is `NUM_EULER`, since 2026-09-25, and what it was waiting on is that a finite
product does not change under a permutation of its indices.** `NUM_CONG n (NUM_POW a (NUM_TOTIENT n))
(SUC 0)` for `0 < n` and `a` coprime to `n`, where `NUM_TOTIENT` is `Modular`'s, the count of `k < n`
coprime to `n`. `NUM_PROD_PERMUTE` asks for surjectivity as a hypothesis beside injectivity, because
deriving the first from the second is a pigeonhole this library does not have, and its induction runs
`NUM_INDUCTION` over a predicate quantifying the map inside, since the step needs the claim at a
different map. The permutation Euler uses multiplies the coprime residues by `a` and **fixes the
others**, which is what keeps the proof to one direction of a coprimality fact. `Euler.scala` is the
derivation and says why each of those; `EulerSpec` detaches the theorem at four and three with
nothing assumed, derives `NUM_TOTIENT 2 = 1` from the definition, and refutes the statement at
`n = 2, a = 2`.

**The arithmetic Goedel's coding needs is `Coding`, and it is finished as of 2026-09-14.**
`docs/adr/0013` decides that the embedded theory is Peano arithmetic and that a finite sequence is
coded by the **beta function** rather than by iterated pairing or by a product of prime powers, on
the criterion that decoding has to be one remainder and therefore Delta-0. What that decision needed
in front of it was not there: the factorial and the fact that every `d <= k` divides `k!`; Gauss's
lemma for a divisor that is merely coprime rather than prime, which `NUM_EUCLID` does not cover; and
the Chinese remainder theorem, which `Modular` has for no moduli at all. All three are there now,
the last over `n` moduli and not only two, and `NUM_BETA_SEQUENCE` is what they were for: every
finite stretch of every sequence of naturals is `NUM_BETA a b i` for two numbers. A theory that
cannot say "sequence" can talk about sequences.

None of it moves the trusted base. Every lemma in that file costs the **two** axioms the naturals
cost, choice and infinity, and `CodingSpec` asserts that as an equality against what each one
inherits rather than as a ceiling.

**The arithmetisation is `Numbering`, and it starts at the pairing.** `docs/adr/0014` decides what
a term and a formula of the embedded theory **are**: numbers, with being one a predicate on `num`,
no datatype and no new type. A constructor of fixed arity codes its arguments with `NUM_PAIR`, which
is Cantor's pairing written on the triangular numbers so that no division appears; a sequence of
unbounded length is coded by the beta function, as `docs/adr/0013` decided. That record also answers
the question a reader arrives with, which is why both are here: **a pair is not a sequence**, and
what 0013 rejected was iterating the pairing rather than the pairing.

The fact the whole construction exists for is that both components of a pair are **at most** the
pair. That is what lets `Descent` define a predicate by recursion on a code, and it is what bounded
quantification over sub-codes in the object theory, which is what Delta-0 means, rests on. The bound is not
strict and `NumberingSpec` derives the number that makes the strict version false rather than
asserting it: `NUM_PAIR 0 0` is `0`. A constructor gets the strict bound back by tagging its code,
which is one step and is also derived there.

**The embedded language starts at `Language`, and `NUM_TERM` is the first predicate of it.**
`NUM_TERM n` says `n` codes a term of PA, and it is defined by recursion **on the number** through
`Descent`, because a term's arguments have smaller codes than the term. A code is `NUM_CODE t p`;
the tags `0` to `4` are a variable, zero, the successor, addition and multiplication, and tags from
`5` are left for the formulas.

The price is not the definition, it is the **admissibility condition** `Descent` asks for, that the
step gives the same answer to two functions agreeing below the index. It holds because every
application of the function inside the step is at an argument the step's own equation bounds, and
proving that is most of the file. `NUM_CODE_LT_RIGHT` bounds the payload and the pairing bounds each
component of it, which is `docs/adr/0014`'s sentence about the bound being the construction's reason
being spent.

`LanguageSpec` asserts that the predicate **refuses**, which is the half that says it is a term
predicate rather than a non-constant one: a code with an unrecognised tag and a code for zero with
the wrong payload are both derived to be non-terms. Both need two numerals of `num` to differ, which
nothing here could say until `Successor.distinct`, and that procedure exists because of those two
assertions rather than the other way round.

**`NUM_FORM` is beside it and the language is complete.** Tags `5` to `8` are an equality of two
terms, a negation, an implication and a universal quantifier over a variable index. Four connectives
and not six: disjunction, conjunction and the existential are abbreviations **in the object
language** rather than syntax, and giving each a tag would mean proving every clause of `Prov` four
more times for nothing.

Two things about it are worth knowing before reading the file. The equality clause asks for two
**terms**, which is the one place the two predicates meet, and it is a side condition rather than a
recursion: `NUM_TERM` is already defined when the formulas are, so that clause costs the
admissibility proof nothing. And the quantifier recurses on the **second** component of its payload
alone, because the first is an index and not a code, which is why the clause descriptor the two
predicates share has four entries rather than three.

`LanguageSpec` asserts the two refusals that say the language discriminates: a **term is not a
formula**, which is what keeping the tag ranges disjoint buys, and an equality whose arguments are
not terms is not a formula, which is the side condition being load-bearing rather than decorative.
Without the second, the predicate would accept any pair at all under tag five and every other test
in the file would still pass.

**`NUM_NUMERAL` is the bridge between the two levels**, and it is the first place a number becomes
a term about that number: `NUM_NUMERAL n` is the code of `S` applied `n` times to zero. A primitive
recursion and not a course-of-values one, because the numeral for `SUC n` is built from the numeral
for `n` and nothing smaller. Every numeral is a term, and distinct numbers get distinct numerals,
which is what makes it a numbering of numbers rather than a function into codes.

Its injectivity is the one induction in the file that `Induct.proveBy` cannot run, and the reason is
worth knowing before meeting it: that driver inducts on the last leading quantifier and leaves the
others **free**, so the hypothesis it gives back is about the same other argument as the goal. This
proof needs the claim at a different one, so it runs `Natural.Induction` directly over a predicate
whose other argument is quantified **inside**.

**The four projections are what a function over codes needs and a predicate over them does not.**
`NUM_TERM` never takes a code apart: it says a code **is** `NUM_CODE t p` for some `t` and `p` and
works under the existential. A function has to produce an answer built from the parts, so it has to
name them, and `NUM_FST`, `NUM_SND`, `NUM_TAG` and `NUM_PAYLOAD` are those names. Each is chosen by
`select` the way `NUM_GCD` is, and what pins the choice down is the injectivity of the constructor
it undoes; at a number not of that shape the choice falls somewhere and nothing is provable about
it, which is the silence `NUM_GCD ZERO ZERO` already leaves.

**`NUM_SUBST_TERM i t s` is the first function over codes**, and what the projections were built
for. The thing to understand before reading it is that its guards are **equations about `s`** and
not about its tag. `NUM_TAG s = 2` would be the natural way to write "the tag is two", and the
recursion would not be admissible with it: at a number that is not a code, `NUM_TAG s` is a choice
that could fall on two, and then the branch recurses at `NUM_PAYLOAD s`, which nothing bounds.
Written as `s = NUM_CODE 2 (NUM_PAYLOAD s)` the guard says the shape, the constructor's two bounds
bound the parts, and the recursion descends.

It is **blind to capture**, and that is sound here rather than overlooked: what Goedel's argument
substitutes is a numeral, which is closed. An open term would need a freshness condition this
development has not got and no consumer wants.

`NUM_SUBST_FORM` is beside it and the pair is complete. Two of its four clauses are worth knowing.
The **equality** clause calls the term substitution and does not recurse, so it costs the
admissibility proof nothing, exactly as `NUM_FORM`'s equality clause costs its own nothing. The
**quantifier** clause compares the bound index with the one being replaced and leaves the formula
alone where they agree, which is what makes it a substitution for a **free** variable; the
comparison is between two variables, so it stays a conditional in the published statement and the
caller decides it.

**`Peano.NUM_STRONG_INDUCTION` is what the level above needs and what `Natural.Induction` is not.**
To prove a claim at `n` it lets you assume it at every smaller number, which is what a fact about a
term's code needs: the codes inside it are smaller numbers rather than predecessors. It is derived
**without** the least number principle and without a classical step, which is not the usual route:
the usual one takes a least counterexample and needs "not everywhere" to give "somewhere not". This
one runs the ordinary induction over `!m. NUM_LT m n ==> P m` and reads the conclusion off at
`SUC n`.

Its first consumer is `NUM_SUBST_TERM_TERM`, that substituting a term into a term gives a term.
Ordinary induction cannot reach it: the claim at a code follows from the claim at the codes
**inside** it, and `NUM_CODE 3 (NUM_PAIR a b)` has `a` and `b` below it by the pairing's bound and
the constructor's, neither of which is its predecessor.

`NUM_SUBST_FORM_FORM` is the same for formulas, and it is what the induction scheme of PA needs
before that scheme can be stated: every instance of it is a formula built by substituting into
another one, and a scheme whose instances might not be formulas is not a scheme. Two of its clauses
differ from the terms'. The **equality** clause asks nothing of the induction hypothesis, because
its arguments are terms and what keeps a term a term is a finished lemma. The **quantifier** clause
is the one with a conditional, and where the index matches the formula comes back untouched.

**`NUM_PA` is the axioms of PA, and it is a plain definition after five that were recursions.**
An axiom is one of six fixed codes or an instance of one scheme, so what defines it is a
disjunction; nothing here descends into a code. Robinson's seventh, that every non-zero number is a
successor, is absent and not missing: it follows from the scheme, which is what makes this PA and
`docs/adr/0013`'s decision.

What that buys is a measurement rather than a convenience: all eight of its facts cost **zero
axioms**, where everything else in the development costs the naturals' two. Membership is settled
by unfolding a definition and picking a disjunct, and that is the same fact as "PA is recursively
axiomatised" seen from the inside. `LanguageSpec` asserts the split in both directions, since a
fact that quietly stopped spending the recursion would be as much a defect as one that started.

`NUM_PA_FORM` is the ninth and the obligation the set owes: an axiom is a formula. It costs the
two, and the pair is the split the paragraph above describes seen in one place. What makes it
worth deriving rather than assuming is that the six codes are nests six deep, so this is the one
claim about them a reader cannot check by eye. It is also where the refusal comes from:
`~(NUM_PA (NUM_CODE 1 0))` is the contrapositive against a code already known not to be a formula,
three lines rather than the seventy the term and formula refusals cost.

The codes and their well-formedness proofs come off **one** tree. The six were written through
text-building functions first, which is fine until something has to prove a code is a formula, and
then the grammar is written twice: once as text and once as a composition of the introduction
rules. `Obj` is the tree, `render` gives the text a reader checks by eye, and the prover walks the
same tree. A constructor added without a case in the prover does not compile.

**`NUM_FREE_TERM` and `NUM_FREE_FORM` say where a variable occurs**, and they are the first
recursions here that answer with a **proposition** rather than a code. They exist because two of
the logical axioms cannot be stated without them: specialisation asks that what is substituted be
closed, and the quantifier's axiom asks that the index not occur in the antecedent. Both are
conditions on occurrence, and nothing in this development could say one.

They are also what the substitution's blindness to capture is measured against. `NUM_SUBST_TERM`
replaces every occurrence without asking whether the replacement is captured, which is sound for a
closed replacement and for nothing else; until these landed, "closed" was said in a docstring
rather than stated.

Nothing new was needed to build them. The substitutions were already a recursion over codes with
parameters and guards that are equations about the code, and the only thing specific to them was
the type of the answer. `defineShaped` and `shapedIsAdmissible` take that type now, and the
substitutions come out at the same inference counts they had before, which is how the change was
checked.

**`NUM_LOGIC` is first-order logic with equality, and every one of its eight is a scheme**, where
PA had six fixed codes and one. Three propositional (weakening, distribution, contraposition, which
with modus ponens give the deduction theorem and make the system classical); three about the
quantifier (specialisation, its distribution over an implication, and generalising a formula the
index does not occur in); and two about equality. Two and not six, because reflexivity and one
replacement scheme give symmetry, transitivity and the congruence of every function symbol, so
writing `x = y ==> S x = S y` and its siblings as axioms would be writing down consequences.
Conjunction, disjunction and the existential get nothing because they have no tags: they are
abbreviations in the object language, which is `NUM_FORM`'s decision being spent, and since
2026-09-16 they are abbreviations something expands.

**The six that expand them are `NUM_AND`, `NUM_OR`, `NUM_EXISTS`, `NUM_LESS`, `NUM_ALL_BELOW` and
`NUM_EXISTS_BELOW`, and the bounded quantifier is what they are for.** Each is a constant of this
logic that builds a code, the way `NUM_NUMERAL` is; none adds a tag, and the `NUM_FORM_` fact
published about each derives that what comes out is a code the four tags already accept. Six
definitions and no axiom. `docs/adr/0021` is the decision.

**Two places said for two days that those three were abbreviations, and nothing built one.** No
constant, no constructor of the `Obj` tree, no helper: a reader met the sentence and took it for a
description of something implemented. Nothing fails on a claim of that shape, because an
abbreviation nobody expands looks exactly like one nobody has needed yet.

**What forced it is that the object signature has no relation symbol at all.** `docs/adr/0014` says
the theory has to take a code apart with bounded quantifiers alone, since that is what keeps `Prov`
Sigma-1; but `i < t` has to be written `?z. i + S z = t` and the existential has to be written
`~!z.~(...)`, so a bound is three abbreviations deep and neither of the two under it existed. The
witness index `z` is an **argument** rather than a fixed number, because a fixed one would want a
freshness condition on both sides that nothing here can discharge: `Language.notFreeIn` walks a
concrete closed code and refuses precisely the codes that have a free variable in them.

**`NUM_LESS` is not `NUM_LT`, and the two cannot be confused by accident.** `NUM_LT` is the ambient
order on `num`, a predicate, and it is what the meta level reasons with; `NUM_LESS` is a function
into `num` that builds a piece of object syntax, and it is what the embedded theory reasons about.
Their types differ, so reaching for the wrong one is a type error rather than a theorem about
something else. That is the defence this repository did not have when `NUM_PRIME_FACTOR` and
`NUM_PRIME_DIVISOR` were a letter apart.

**The twelve clauses saying where an index occurs free in one of the six and what a substitution
does to it landed on 2026-09-16**, so the six are abbreviations something both expands and reasons
about. Twelve facts, no axiom, no constant: each is proved by rewriting both sides of its published
statement with the six defining equations and the nine clauses of the family it extends, and
splitting on a guard only where the two do not meet.

**Seven of the twelve need that split and five do not, and the prediction was three.** What decides
it is not whether the constant binds an index but whether the published answer carries a `COND` the
rewriting has to put somewhere. `NUM_FREE_FORM_EXISTS` binds and needs no split, because the
quantifier's own clause already produces the conditional in the shape that gets published;
`NUM_SUBST_FORM_EXISTS` needs one, because what comes out of the rewriting is a negation applied to
a conditional and what a consumer wants is a conditional between two negations. Four of the six
bind an index and two do not, which is also not the three and three the file said while the twelve
were names without statements.

The reduced form is what is published rather than what the rewriter produces, and that choice is
the whole cost. `NUM_LESS z s t` introduces an occurrence of its own witness, so the rewriting
answers `(NUM_FREE_TERM i s \/ (z = i)) \/ NUM_FREE_TERM i t` where a consumer wants `s` and `t`
named and nothing else; taking the middle disjunct out is what needs the split, and two units of
disjunction that nothing in the logic publishes.

**What says a guard is load-bearing is a consequence of the right clause that the guard-dropped
one contradicts, and there is one per guarded clause.** Eight of the twelve carry a `COND`, which
is the four binding constants times two families, and `LanguageSpec` names all eight: a quantifier
binds its own index, a comparison leaves nothing free at its witness and replaces nothing there,
a bounded quantifier reads its bound under that same witness, and a substitution for the witness
leaves the bound alone. The other four are `NUM_AND`'s and `NUM_OR`'s, which bind nothing and have
no conditional for a consequence to be about; they are held by the two assertions that run over
every published statement, and that is the whole of their coverage.

**The sharper attack is not in the tree and this file said it was, from the commit that added
it.** Stating each clause with a guard dropped and checking the derivation refuses it is the
direct test, and a spec cannot run it: `connectiveClauses` derives the statement published under a
name, so nothing can hand it a statement nobody published. It was run outside the tree on
2026-09-16, one guard-dropped statement per guarded clause and eight refusals, and it is a
measurement with a date rather than a guard. The
sentence that claimed `LanguageSpec` did it was contradicted by `LanguageSpec`'s own docstring on
the day both were written.

**`NUM_CLOSED t` is what the substitution's blindness to capture costs, written down.** **Two** of
the eight schemes carry it, specialisation once and replacement twice; this sentence said three
until 2026-09-15, which was three occurrences of the condition counted as three schemes. PA's
induction scheme substitutes as well and needs no condition, putting `0` and `S i` where `i` stood:
neither can capture, the first having no variables at all and the second only the one being
replaced. The condition is **stronger** than the textbook one, which asks merely that the term be
substitutable, and the difference is a real loss: the object system cannot instantiate a universal
at a variable. What is not lost is Goedel's argument, which substitutes numerals. Lifting the
restriction wants a substitutability predicate, which is a recursion over the formula this
development has not got.

**And until 2026-09-15 nothing could discharge the condition**, which is a defect that fails no
test: a scheme whose side condition is unmeetable is a theorem, and the eight were all provable
while two of them were usable at exactly one term. That term was the object language's zero, closed
by fifteen lines walking the freeness clauses inside `LanguageSpec`, in the test that needed an
instance of specialisation and had nowhere else to get one. `NUM_NUMERAL_CLOSED` is the family
those lines were an instance of, and the family rather than the instance is what Goedel's
argument needs: argument substitutes the numeral **of** a number, and there is one of those per
number, so a development that can close the numeral of zero and no other cannot state that PA
proves anything about its own arithmetic.

A scheme is a value rather than text. `Scheme` carries its binders, its conditions and its tree,
and the two shapes it is read in come off it: the existentially quantified disjunct inside the
definition, and the universally quantified statement a caller wants. `schemeMembership` walks from
the second to the first once for all nine schemes there are, and `everyMemberIsAFormula` proves
`NUM_PA_FORM` and `NUM_LOGIC_FORM` with the same walk. Both were bespoke for PA first and both come
out at the same inference counts after the generalisation, which is how it was checked.

**`Provability` is what the embedded theory can prove, and it is a development of its own** rather
than more of `Language`, because it is about that language rather than part of it: nothing in it
declares a constructor or a predicate of the object syntax.

**Not one of its three definitions is a recursion**, and that is the whole return on
`docs/adr/0013`. A derivation is a finite sequence of formulas, and a definition that had to walk
one would recurse on the length. The beta function removes that: a sequence is two numbers,
`NUM_BETA a b j` is its `j`th entry, and quantifying over the entries is quantifying over an index.
So `NUM_STEP`, `NUM_PROOF` and `NUM_PROV` are formulas with their subjects free, exactly as
`NUM_PA` and `NUM_LOGIC` are, and all three cost no axiom.

A proof carries the index of its **last step**, not its length. Writing the length instead would
put `0 < k` and a `k - 1` into every statement about a proof, and subtraction on `num` is
truncated, so that is a guard and an asymmetry bought for nothing.

Two rules of inference, modus ponens and generalisation, which with the eight schemes are a
complete Hilbert system. Each rule needs a step **earlier** than the one it justifies, and that
bound is the only thing making a derivation well founded. `ProvabilitySpec` is what says so:
at index zero neither rule can apply, so the four-way disjunction collapses to the two axiom
clauses. Drop either bound and every formula becomes provable while every other test still passes.

What is there and what is not. The predicate is **inhabited**: every axiom is provable, by the
derivation that is one line long, and that is the first thing anywhere to spend
`NUM_BETA_SEQUENCE`. Since 2026-09-14 it is **closed under both rules of inference**: under modus
ponens, `NUM_PROV (p ==> q)` and `NUM_PROV p` giving `NUM_PROV q`, which is the first thing here to
put two derivations into one sequence; and under generalisation, `NUM_PROV p` giving
`NUM_PROV (NUM_CODE 8 (NUM_PAIR i p))`, which is the same construction with one block instead of
two. Those two rules with the eight schemes are the whole Hilbert system, so what the predicate
holds of is closed under everything the embedded theory can do.

The second is the short half rather than a second copy of the first, and the difference is one
sentence: a single derivation keeps its numbering, so nothing is shifted and none of the arithmetic
of where a join falls appears. They are written over one toolkit for that reason, which
`Provability.closures` explains, and the second landed as that toolkit plus forty lines.

**That closure is not D2, and this file said it was.** Goedel's second derivability condition is a
theorem **of PA**, the implication written in the object language and derived inside it, which
`docs/adr/0013` states in as many words and lists among the object-level work it calls a piece of
its own. What landed is the same shape one level up: an implication of the ambient logic about the
`NUM_PROV` predicate, saying that the coded predicate behaves like a theory rather than like a set
of axioms. It is what every meta-level argument about the embedded theory chains with, and the
object-level derivation of D2 is not written. Read as D2 it makes the remaining work look done.

**`NUM_STEP_SHIFT` is the hard part of that closure**, and it landed before the closure itself.
To put two derivations end to end their steps are renumbered, and a step's
justification names earlier steps **by index**, so every one of those indices moves too. The lemma
says a justified step survives the move, and what makes it work is that the bounds move with them:
`x < j` gives `c + x < c + j`. That is `Peano.NUM_ADD_LT_MONOTONE`, the first thing `Provability`
has needed from `Peano` that was not already there, and it is derived from the non-strict version
rather than by a second induction.

One lemma and not two. The first block of a concatenation keeps its numbering and the second does
not, and the unshifted case is this lemma at a shift of zero; `ProvabilitySpec` derives it that way
rather than stating it, which is the assertion that the general lemma really covers the special
case. The agreement it asks for is only up to `m`, which is the whole point: a concatenated
sequence does not agree with either half past that half's own last step.

`Peano` gained three order facts for that concatenation. `NUM_LT_NOT_LE`, that the strict order
excludes the other one, which is what makes a case split on `NUM_LE m n \/ NUM_LE n m` a split
rather than two overlapping cases; `NUM_LE_ADD`, that a summand is at most its sum, which holds on
`num` with no side condition because there are no negative numbers; and `NUM_ADD_LE_CANCEL`, which
is `NUM_ADD_MONOTONE` read backwards.

The third is worth a line, because it is the one obligation the written plan for the closure had
not accounted for and it was invisible until the derivation reached for it. An index `j` past the
join is the second block's index `j - c`, and saying that `j - c` is inside that block's own bound
means cancelling `c` out of `j <= c + k2`. Nothing did. `NUM_ADD_CANCEL_LEFT` cancels a summand out
of an **equation**, which reads like the same fact and is not one. It costs three lines for the
reason `NUM_ADD_MONOTONE` does: `NUM_LE m n` **is** `?d. m + d = n`, so the premise's witness is the
conclusion's and one associativity is what happens in between. The route through trichotomy and
`NUM_LT_NOT_LE` reaches the same place, is longer, and makes a classical case split out of a
statement about a difference.

**`Deduction` is where derivations OF the embedded theory are built, and it is the first link that
declares nothing.** `docs/adr/0013` decided that a development whose product is object-level
derivations is its own piece of work rather than a helper inside whichever development first needs
one, and this is that development. No type, no constant, no definition, no axiom, so it **does not
become** the widest signature: the last link and the widest signature stopped being the same thing
when this landed. Which development is widest is `Chain.widest` and is written nowhere else, for
the reason the note on `Chain.widest` near the start of this file gives. `DeductionSpec` asserts
the theory it hands on is the one it was given, constant for constant, so a definition arriving
here goes red rather than passing unnoticed.

It holds five schemes, each proved once for **every** formula rather than at a code. `NUM_PROV_SELF`,
that PA proves `p ==> p`, which is three lines because the system has no reflexivity for implication
and getting there from weakening and distribution is the standard exercise. `NUM_PROV_SYLL`,
that provable `p ==> q` and provable `q ==> r` give provable `p ==> r`, which is the rule every
derivation of any length is made of. And three more that exist for one purpose: they are what the
**deduction theorem** is assembled from, one per way a step can be justified. `NUM_PROV_WEAKEN` for
the axiom cases, `NUM_PROV_IMP_MP` for the modus ponens case, and `NUM_PROV_IMP_GEN` for the
generalisation case, which carries `~(NUM_FREE_FORM i h)` because without it the rule is false.

**The deduction theorem is proved**, and it is what makes building object derivations tractable: to
get `h ==> p` you assume `h` and work forwards. `Provability` gained `NUM_STEP_FROM` and
`NUM_PROV_FROM` for it, two definitions rather than three, because nothing will ever quantify over a
derivation-from-a-hypothesis as a single number the way `NUM_PROOF` exists to allow. The proof is
strong induction on the step index and its five cases are five one-liners, which is the return on
proving the four rules separately first.

Two conditions on the hypothesis and they differ in kind: that it is a formula, which every scheme
of `NUM_LOGIC` asks; and that no index occurs free in it, which is the restriction the textbook
statement carries and without which the theorem is false. The second is spent in exactly one place,
`NUM_LOGIC_VACUOUS` inside `NUM_PROV_IMP_GEN`.

**`NUM_STEP_FROM` asks that a step be a formula and `NUM_STEP` does not**, which is a decision and
is recorded where it is made. The three rules each need their formulas to be formulas, and the
alternative was inverting `NUM_FORM_CASES` at two tags, which is the general fix and is two lemmas
of seventy lines. What it leaves behind is worth knowing: **nothing rules out `NUM_PROV` holding of
a code that is not a formula**, and those inversion lemmas are what would settle it.

**And the condition is dischargeable**, which it was not for the first hours of the theorem's life.
`Language.notFreeIn` walks a concrete code through the nine freeness clauses and returns
`!i. ~(NUM_FREE_FORM i c)`, so `DeductionSpec` applies the theorem to an actual axiom of PA with
**nothing** left assumed. The only case it can fail on is a variable no enclosing quantifier binds,
which is a code that is not closed, and it refuses there by naming the index.

**PA proves its own arithmetic on numerals, and since 2026-09-18 that is both operations.**
`NUM_PROV_NUMERAL_ADD` came first and called itself the first brick of Sigma-1 completeness;
`NUM_PROV_NUMERAL_MUL` is the second, and the order between them is not a preference. The step of
the multiplication's induction turns `t * S u` into `t * u + t`, so the hypothesis travels into the
left summand of a sum, which is `NUM_PROV_ADD_CONG`, the successor congruence one arity up. What
stands there is then a **sum of two numerals**, which is exactly the statement the first brick
settles. `DeductionSpec` asserts that with `Derivation.restingOn` rather than by reading the proof.

Both multiplication axioms had to be put to work first, which is the difference between a fact about
a code and a fact a derivation can use: `NUM_PA_MUL_ZERO` says `!v0. v0 * 0 = 0` and
`NUM_PROV_MUL_ZERO` is that axiom at a closed term. The successor one is where the substitution
walk is longer than addition's, because `v0 * S v1 = v0 * v1 + v0` puts a product **inside** a sum
and the walk descends through both. Four facts, **zero axioms**, and the trusted base stays at
nineteen.

Why it is the bottom of the stack rather than a lemma somebody wanted: every pure-arithmetic
representation `docs/adr/0013`'s coding needs, which is `NUM_TRI`, `NUM_PAIR`, `NUM_CODE` and the
projections, is written with `*`. While the object theory could add its numerals and not multiply
them, nothing above could be shown to represent anything.

The quantifier is the only interesting clause, and the bookkeeping is the whole of it: descending
past `!b. ...` carries `~(b = i)` down, and `NUM_FREE_TERM i (NUM_CODE 0 b)` is `b = i`, so the
inequality carried down is exactly what refuses the variable at the bottom. Shadowing works because
the list is prepended to, and `LanguageSpec` asserts that rather than leaving it to a reading: none
of the codes this repository builds binds one index twice. Above that is the thing Goedel's
argument actually needs, `Prov` as a formula **of the object language** with one free variable
rather than as the predicate `NUM_PROV` of the ambient logic, and it is not written.
**D1, D2 and D3 are statements about that formula, so not one of the three can be stated yet.**

**The road to that formula goes through truth, and the first half of it is `Truth`, since
2026-09-25.** `docs/adr/0040` is the decision: a representation of one of the constants the stack
uses is a formula of the object language with a theorem that its **truth** is the predicate, and
what turns a true formula into a provable one is completeness for bounded formulas, proved once,
rather than a derivation in PA per constant. `NUM_VALUE t e` and `NUM_TRUE p e` are the value of a
term and the truth of a formula at an environment `e : num -> num`, both recursions on the code
answering with a function of the environment, which the quantifier's clause forces: it reads the
body at `e` updated at the bound index. `NUM_TRI_GRAPH`, the code of `v0 + v0 = v1 * S v1`, is the
first representation, and `NUM_TRI_GRAPH_TRUE` says its truth is `e 0 = NUM_TRI (e 1)`. It is a
link, between `provability` and `limit`, and not a development beside the chain: that standing is
for the constants of one investigation, which is what `ChainCoverageSpec` says of it.

**Where truth first meets provability is the closed terms, since 2026-09-25.** `NUM_PROV_VALUE`
says PA proves every closed term equal to the numeral of its value, by course-of-values induction
on the code: each operand is replaced by its numeral under a congruence, and the two numerals are
settled by `NUM_PROV_NUMERAL_ADD` or `_MUL`. The congruences it needed on the right of a sum and on
both sides of a product were not there and are `Deduction`'s now, beside `NUM_PROV_REFL`.
`NUM_PROV_TRUE_EQ` follows: a true closed equation is provable. That is completeness for the
atomic formulas that hold and nothing more. `NUM_TRI_GRAPH_TRUE` still says only what its formula
means: its instances are equations between terms that are not closed until a numeral is put in
for each variable, and no lemma here yet relates the truth of a substituted formula to its truth
at the environment the substitution describes.

Not written above that: a false closed equation with a provable negation, which wants PA to prove
two different numerals different; the connectives and the bounded quantifiers of completeness for
bounded formulas; any representation other than `NUM_TRI_GRAPH`; the object-level `Prov`, and so
neither the diagonal lemma nor D1, D2 and D3. `docs/adr/0013` says why the last of those is its own
piece of work rather than a helper inside this one. The order of that work is kept in Mycelium, in
card `4102f131` and its parent `89712313`, and not here: a list of what is missing goes stale
silently, because nothing fails when an item on it gets built.

**The set defined by rules is `Inductive`, a link since 2026-09-16.** This sentence said it was
`Chain.widest` until 2026-09-17, in the same text as the paragraph that says the name of the
widest development is not written in prose because it had already gone stale twice.
That makes three, and the same day found three more of it in the sources: `Chain`'s own docstrings
had `Transcendental` and `Reaching` as the widest and `Inductive` as the last link, while the field
read `forward`. `DocumentationSpec` compares the claim against the field now, so a fourth goes red
rather than being read. One
definition in three of rewriting theory is given in the shape "the least subset containing X and
closed under these clauses", and until this landed that shape could not be **written** here. What
could be done instead was to generate the closure forwards and look, which answers a membership for
whatever the budget reached and answers **nothing** about a non-membership. `INDUCTIVE f` is the
intersection of every `f`-closed set rather than an iteration, which is `Natural.NUM_REP`'s trick
taken away from the one operator it was written for; `docs/adr/0020` is the decision and what it
rejects is the Kleene iteration, which wants ordinals or a finitarity hypothesis the motivating
clause does not satisfy. Two constants, no axiom.

The two faces are two facts because they cost different things, and the asymmetry is the whole
point. `INDUCTIVE_INDUCT` asks **nothing** of `f` — it is the definition unfolded and specialised —
and it is what proves a non-membership. `INDUCTIVE_INTRO`, the introduction rules of the rule set
all at once, asks `MONOTONE f`. `INDUCTIVE_FIXPOINT` is the two together and is derived from them.
`InductiveSpec` runs both halves on the even numbers, and the membership is not decoration: a
definition whose extension was empty would satisfy every induction principle and every
non-membership above it, so the one test that has to be a membership is the guard against the whole
file being vacuous.

**The monotonicity it does not carry is `Monotone`, a procedure rather than a development, since
2026-09-16.** `INDUCTIVE_INTRO` asks `MONOTONE f` and every operator written from a rule set in the
usual shape — a disjunction of clauses with the set argument only positive — is monotone for reasons
visible in the term. `Monotone.prove` walks the term and produces the theorem; it **recognises a
shape and decides nothing**, so an operator it refuses may still be monotone and the refusal names
the offending subterm rather than the operator. The two hand proofs it retired were **52** code
lines in `InductiveSpec` and **56** in `Reaching`, and the pair rather than either figure is the
argument: the second operator is much larger and its proof was four lines longer, because everything
to the right of the one positive occurrence is carried across without being looked at. `docs/adr/0020`
predicted forty and seventy for that pair and is corrected in place. The refusal is exercised on
`\S x. ~(S x)`, where `InductiveSpec` also derives `~(MONOTONE ...)`, so the refusal is a fact about
that operator and not this procedure being careful.

**What `Inductive` was built for is `Reaching`, a link of the same day.** `REACH R A x q` says
`FST q` is reachable from `x` under `R` spending exactly `SND q` steps of a distinguished
sub-relation `A`, so the reflexive-transitive closure and the length of a derivation are one
construction rather than two: at `A := R` the counter is the length, and `?k. REACH R R x (PAIR y k)`
is the closure. One constant, no axiom, and **no recursion on `num` anywhere in it**, which is what
defining a closure rather than iterating it buys: the induction over a derivation is
`INDUCTIVE_INDUCT` at this operator and nothing unfolds a number.

What it hands over is the potential-function lemma, and its second hypothesis is the half to read
before reaching for it. A measure `Phi` that drops by exactly one across a counted step, written
`Phi u = SUC (Phi v)` so that no subtraction appears, and that **does not fall** across any other
step gives `Phi x <= SND q + Phi (FST q)`. The card that asked for the file wrote "does not rise",
which is true, unusable and points the other way, and it is unmeetable for the system the work was
for, where two of the eleven rules raise the measure. `ReachingSpec` derives the counterexample
rather than asserting that the hypothesis cannot be dropped, which is the only form a negative
control can take here: a theorem does not refuse.

**It is instantiated since 2026-09-18, and the instance is `Collatz.S2_RUN_POTENTIAL`**: this
lemma at `R := S2_RUN`, `A := S2_RUN_COUNTED` and `Phi := S2_PHI`, so a run of the rewriting system
from `x` is known to spend at least `S2_PHI x - S2_PHI (FST q)` commutations getting where it got.
The paragraph on `Collatz` below says what that cost. `Forward` still builds `WORD_RFC` out of
`INDUCTIVE` directly and never mentions `REACH`, which is not an omission: a membership in the
closure and the length of a run that reaches it are two questions about one system, and only the
second needs a counter.

**The one rewriting system this repository is about is `Collatz`, and since 2026-09-16 its marked
words are closed under a step.** `Forward` gives the right forward closure of an arbitrary system,
`WORD_RFC R`; `Collatz` is the one `R` an investigation is about, the eleven rules of $S_2$ over
seven letters, generated from `collatz@8b991e5` `code/referee/checks_rewriting.py` rather than
transcribed. It sits **beside** the chain, which is a decision rather than an accident: eleven
rewriting rules of a Collatz encoding do not belong in the vocabulary a question about the reals is
typed in, so `Ask` and `Find` cannot reach it and `CollatzSpec` is the only thing that builds it.

**The marked words are where the potential argument stops being false, and the anchored words are
where it is true.** `S2_MARKED w` says `w` has exactly one tail marker and it is the last letter,
and outside that class the argument is false with the witness the source names: `/ff.012` rewrites to
`/0.012` and the potential falls by three, which no counted step pays for. `S2_MARKED_CLOSED` is
what says a step never leaves the class. What the class does **not** say is that the head marker is
the first letter and occurs nowhere else, and `REACH_POTENTIAL` needs that in both of its
hypotheses: `f0.` is marked, `A2` takes it to `0f.`, and `S2_PHI` is zero on both, where the first
hypothesis asks for a drop of exactly one; `0/0.` is marked, `B1` takes it to `0/t.`, and the
potential falls, where the second asks that no uncounted step lower it. The first happens because
`NUM_SUB i 1` is truncated, so a digit at position 0 and one at position 1 both contribute nothing,
and without a head marker in front a digit can sit at position 0; the second because the three `B`
rules fire at **any** occurrence of `/`.

**Those two witnesses are derivations since 2026-09-21, and what they replaced is a reading.**
`Collatz.ClassWitnesses` is the pair, nine theorems each checked against the text it is written
down as saying, and `CollatzSpec` is what reads them: marked, not anchored, stepped, and the
conclusion of the published lemma refuted at that pair. The half that costs something is
`~(WORD_STEP S2_COUNTED (0/0.) (0/t.))`, a **negative** about a relation, which naming `B1` does not
give and which `Collatz.noCountedStepFrom` derives: every commutation's left-hand side is a marker
followed by a digit, and `0/0.` holds no marker anywhere, so the rule cannot have fired at
`WORD_LENGTH x` for any context at all.

**There are two readings of that block and the second landed on 2026-09-22.** This paragraph said
until then that the argument does not reach a word holding an `f` or a `t`, and the card that asked
for such a word said it would want the enumeration of `WORD_LENGTH x`. It does not: the letter read
is the block's **second** rather than its first, a word with no `0`, `1` and `2` cannot supply that
one either, and it is the same walk with the offset in it. `/ff.` is derived at that offset in
`CollatzSpec`, and `tools/verify/perturb-the-other-end-of-the-block.sh` is where the two readings
are each seen carrying a test the other does not. What is **not** reached is a word holding a marker
**and** a digit, `/f0.` being the smallest, and that one is refused by name. Until 2026-09-21 the two sentences rested instead
on six figures measured over every word of at most seven letters, no sampling: of the marked words'
44790 counted steps, 9330 failed the first hypothesis, and of their 33281 uncounted steps, 14454
failed the second, against **0 of 3516** and **0 of 3280** once the head condition is added. No test
read them, and a figure of that shape is a property of the enumeration's bound as much as of the
system. So the class part C stands on is the marked words **and** one head marker in front.
That predicate is `S2_ANCHORED`, positive length with the head marker at position zero and at no
later one, and `S2_ANCHORED_CLOSED` is its closure lemma; `S2_HEADFREE` is to it what `S2_TAILFREE`
is to the marked words, which is what makes the two constructions one read at two letters.

Two things about that proof are worth knowing before opening the file. **A tally is the wrong
instrument and an earlier plan reached for one**: `S2_MARKED` is positional, so a count of markers
equal to one does not say the marker is last, which is half of what the predicate asserts. What the
proof runs on is `WORD_CONCAT_NTH_LEFT` and `WORD_CONCAT_NTH_RIGHT`, which speak about positions;
`WORD_CONCAT_TALLY` is still the right lemma for `S2_PHI`, which is a sum. And **`NUM_ONE_SUC` is
never applied to a whole statement here**, because three of the eleven rules have the letter `1` in
them and the rewriter does not know the difference between a letter and a numeral: a proposition
rewritten with it comes back about a different word. The index is rewritten alone and carried in by
congruence, which is written where a reader meets it.

**Both hypotheses are theorems on that class.** `S2_PHI_COUNTED_STEP` is the first, that a
commutation drops the measure by exactly one, and it spends the anchored class in exactly one place:
the rule fired somewhere and something has to be in front of it for the digit to move towards, which
is true because no commuting rule begins with the head marker. `S2_PHI_PLAIN_STEP` is the second,
over the five rules that are not commutations, and it has three shapes rather than one: the two
consuming rules eat the tail marker, so a marked word has nothing after them and what is compared is
`P` against `P + (|x| - 1)`, which is `NUM_LE_ADD`; `B1` fires at the head and keeps the length, so
the two measures come out as the **same** term and the comparison is reflexivity; `B2` and `B3` fire
at the head and lengthen the word, so every letter after them sits one place further along and
contributes one more, which is `NUM_SUM_MONOTONE_BELOW` over a pointwise split on whether the letter
there is a digit.

**What the instantiation had to decide is where the class goes, and it goes in the relation.**
`REACH_POTENTIAL` asks both of its hypotheses of **every** pair, and a measure that behaves only on
a class has no side condition to put that class in. `S2_RUN u v` is a step of `S2` from a word that
is anchored and marked, `S2_RUN_COUNTED` is one of those that is also a commutation, and the
restriction loses nothing because the class is closed under a step: a run that begins inside it
never leaves. Two constants, no axiom, and `S2_RUN_INHABITED` is the guard, since a bound on every
run of a relation that steps nothing is a theorem about nothing and `REACH_START` would detach the
bound anyway. What is **not** reached is a run of positive length: detaching one wants a refusal of
the counted step at a concrete pair, which is a negative about `WORD_STEP` and nothing here proves
one.

**And the bound is quadratic at the one family this investigation names, since 2026-09-18.**
`S2_FAMILY_BOUNDED` is `S2_RUN_POTENTIAL` at `/f0^j.`, so a run from the `j`th member spends at
least `NUM_TRI j` commutations getting wherever it gets, and `NUM_TRI` grows as the square. What
made it statable is `S2_PHI_FAMILY`, the measure of that family in closed form, and the closed form
is a **triangular number** rather than a quotient: `j (j + 1) / 2` cannot be written on `num`, which
is the same wall `docs/adr/0014` hit and why `Numbering` defines `NUM_TRI` by recursion in the first
place. The two recursions meet without any arithmetic in between, the `j`th zero sitting at position
`j + 1` and weighing its distance from the head. `S2_ZEROS_LENGTH` and `S2_STEM_LENGTH` are what the
induction needs and the second is spent **under a binder**: the weight of a letter is how far along
the word it is, so a block placed after the stem has to know how long the stem is.

Read it for what it is. It is the quadratic **from below**, which is the direction `REACH_POTENTIAL`
gives and the direction a lower bound on derivation length wants; it says nothing about termination
and nothing about a run of that length existing. And `S2_PHI_FAMILY_AT_ONE` is the guard an
off-by-one would fail: `S2_PHI (/f0.) = SUC ZERO` is written by hand and derived through `NUM_TRI`,
where every other fact about the family is stated in `NUM_TRI` and would agree with itself.

**And the two facts that keep it from being a theorem about nothing are published rather than
argued.** A closure statement over an empty class is true and empty, and so is one over a relation
that steps nothing; neither would fail anything else in the file. `S2_MARKED_INHABITED` and
`S2_STEP_INHABITED` are `/0.` and the `B1` step that takes it to `/t.`, and `CollatzSpec` **detaches**
the closure at that pair rather than asserting that an implication exists.

**The digit family is in the closure, and since 2026-09-18 that is a theorem rather than a Python
search.** `S2_FAMILY_TAIL` is `!i. WORD_RFC S2 (/f0^(SUC i).)`, which is section 3.1.30 B of the
investigation's own document; `S2_FAMILY_F` is the induction under it, that `/f0^i f` is in the
closure, and the second is the first plus **one** right extension rather than a second induction.
Three clause instances are the whole proof and the source names all three: `/ff` is `B2`'s
right-hand side, `f|0 -> 0f` is `A2` and grows the run, `f|f. -> 0.` is `R1` and closes it. The run
of zeros is `S2_ZEROS`, a constant of its own defined by recursion on the index, and its two
equations are published because a defined constant whose equations nobody can reach is a name
rather than a function.

**And what keeps that from being a theorem about everything is `S2_RFC_REFUSED`.** A closure that
held of every word would leave both family facts derivable and would say nothing, and no test
anywhere would have noticed: `ForwardSpec` asserts that the induction principle asks nothing of the
system, which is a different claim. `~(WORD_RFC S2 WORD_EMPTY)` is the guard, one induction over the
closure at the invariant "not the empty word", and it costs nothing new: every clause produces a
word with a rule's right-hand side inside it, and `S2_RULE_NOT_EMPTY` already said those have
letters. It is deliberately the weakest such statement there is. The source's instrument refuses
`/f.`, `/ff.` and `/tt.` as well, and each of those wants an argument about which letters may stand
next to which, where this one only counts.

**The eleven rules are derived pairwise distinct, and that is a different question from the count.**
`CollatzSpec` counts eleven disjuncts off the definition, which says how many clauses were written;
the fifty-five separations say how many pairs the relation holds of, and a table in which two rules
had collapsed into one would pass the first and fail the second. They are not published: no consumer
needs the rules to be distinct, it is a fact about the encoding, and facts about the encoding live in
the spec that asks for them.

**The first analysis is `Limit`, and the transcendental functions are `Transcendental`.** Both
landed on 2026-09-15, both are links in the chain, and between them they declare eight constants
and no axiom. `converges s l` is the epsilon-N statement written out and `lim s` is choice applied
to it, pinned by `CONVERGES_UNIQUE` wherever the sequence converges and silent where it does not;
`exp`, `sin` and `cos` are their power series through that limit, `ln` is the inverse of `exp` named
by choice, and `sinh` and `cosh` are `(exp x - exp (0 - x)) / 2` and the same sum, which is the one
pair here that is not a series and is the one thing in `docs/adr/0017` a reader should not skip: what it buys
is `cosh x + sinh x = exp x` today, and what the series would have cost is a rearrangement into
even and odd parts that this repository does not have. `docs/adr/0017` is the decision, and what it rejects is four characterising
axioms, which would have been the first thing this repository asserted about a domain it can
construct.

**What is proved about the six constants is the value of each at zero and, for the hyperbolic pair,
two identities**, and the reason is worth knowing before opening either file: a series at zero stops
moving after its first term, so `CONVERGES_CONSTANT` with `CONVERGES_EVENTUALLY` settles it and no
convergence theorem is involved.

**`MONOTONE_CONVERGES` landed on 2026-09-15 and is the first thing here that obtains a limit rather
than assuming one.** Increasing and bounded above gives convergent, by the least upper bound, and it
is where `COMPLETENESS` is spent the second time; `LimitSpec` asserts that by name rather than by a
count, because a derivation of it that did not reach the sixteenth axiom would be a derivation of
something else. What it cost in front of it was one missing rule of the logic: the step "otherwise
the supremum would not be least" is a negated universal turned into a **witness**, and
`Peano.NUM_ARCHIMEDES` records that this logic had none and that its own derivation was turned
around to avoid needing one. There is no turning this one around, so `Classical.NOT_FORALL` landed
with it, along with `Order.LE_OF_NOT_LT` and `LT_OF_NOT_LE`, which cost nothing classical at all:
on a total order the three cases are on the table before anything is negated.

**That a series converges is `SUM_COMPARISON`, since 2026-09-16, and this paragraph said nobody had
assembled it for as long as it existed.** Non-negative terms under a series whose partial sums are
bounded: `SUM_SUC` makes the partial sums increase and `SUM_MONOTONE` carries the domination to
them, so it is `MONOTONE_CONVERGES` spent on the one sequence a series always has, three published
facts in one order and no new machinery. `CONVERGES_LE` and `CONVERGES_GE` are what say **where**
such a limit is, and they landed with the test's first consumer because the test alone cannot: it
hands back `?l. converges (Sum f) l`, and an existential is not a bound. Their hypothesis is a
bound the terms respect from an index on rather than everywhere, and that is the whole of their
usefulness: the lower bound worth having on an increasing sequence is one of its own terms, which
is false below that term's index.

**Whether a series converges is decided over a named fragment since 2026-09-25, and in both
directions.** Until then the answer set was {converges, silence}: nothing in the proof side could say
that a series fails to converge, and `?l. converges (Sum f) l` went to no procedure at all, because
`Prove.addressOf` had no address for it and matching it against `SUM_COMPARISON` determines `f` and
nothing about the dominating series. `diverges` is a constant of `Limit` now, and the criteria are
published there in both directions and derived in `Criteria`: the term test, the geometric series at
a symbolic ratio **with its value** `inv (1 - q)` and its divergence from magnitude one up, the ratio
test and its other side, and a constant factor carried in and out. The powers of a fraction vanish
without an Archimedean step, because their limit equals its own multiple by the fraction.

`Convergence` is the procedure and `Prove.Address.Series` is where the three shapes of the question
go. **It reads a summand against closed forms and does not apply the ratio test**, because applying
the ratio test is a derivation per shape at a symbolic index and every closed form already has a
published theorem; so the hypergeometric terms are outside the fragment and refused by name, a
rational function of the index is refused as the class where the ratio tends to one, and a goal the
procedure refutes comes back as `Denied`, carrying the theorem. A goal naming a value other than the
one the procedure proved is `NotEqualTo`, decided, where both values are numbers built from
numerals, and `ValueUnidentified`, not decided, where either holds an atom such as `exp 0`: the
four are listed in `Convergence`'s docstring with which of them are decisions.
`docs/adr/0041` is the decision. **A polynomial in the index times a geometric term is in the
fragment since the same night**, `docs/adr/0045`: degree one is the ratio test, which is that
test's first consumer outside a spec, and each degree after it is a comparison that spends
`CONVERGES_BOUNDED`; the procedure names no value for these and says so when a value is asked.
`Conjugacy.GAMMA_CONVERGES` is the Collatz series it made
statable, and it is one direction of section 3.1.10 B in the form the comparison test gives, which
that file says in its first paragraph.

**`Transcendental.EXP_ONE_ABOVE_TWO` is `2 < exp 1` and it is proved, since 2026-09-20.** It is
the first fact here about a value this repository does not compute: every other one is a value at
zero, where the series stops after a term and no convergence question arises, and this one needs
the series to converge before `lim` says anything at all. `SUM_COMPARISON` obtains that, which is
the first time anything spends it on a series of this file, and `CONVERGES_GE` puts the third
partial sum, `1 + 1 + 1/2`, under the limit.

**What it waited on was arithmetic and not analysis**, and the sentence that stood here until that
day is worth keeping in that form: the comparison test had been provable and unspent since
2026-09-16, and what was missing was the dominating series. Putting `1 / i!` under `2 * (1/2)^i`
is `2^i <= 2 * i!`, which is `Coding.NUM_POW_LE_FACT` and is one induction on the shifted claim
plus `NUM_CASES` rather than the two-base induction it looks like. The order half was
`INV_ANTITONE` with `LE_MUL_BOTH` under it, landed 2026-09-18. **That sentence was written in
seven documents and went stale in all of them at once**, which is the defect this file names
about a fact written twice. The figure here said five for a day, and so does the title of
`9734bf7`, the commit that landed the second fact and made the copies false. Five is what that
commit repaired; the population was seven, and the two it left behind stood for the seven hours
between that commit and `ceedf4d`, on the same day. The instrument is the union of the two
commits' own diffs rather than a pattern, because the claim is spelled differently in every
document and a pattern matching all of them would have been built by reading them, which is the
reading it was meant to replace. A count of copies is itself a copy, and this one counted the
repair instead of the population, which is the shape of error the sentence it sits in is about.

**The Cauchy product is proved, in two theorems, and both landed on 2026-09-21.**
`Limit.SUM_CAUCHY_PRODUCT_NONNEG` is the case where both series have non-negative terms and
`SUM_CAUCHY_PRODUCT` is the case where they do not, the second asking absolute convergence of
both. The order between them is the whole design and not a sequence of attempts: the general one
spends the non-negative one **once**, on the magnitudes, and gets from it a sequence that is
known to vanish.

**Neither of them has an epsilon in it**, which is the return on the route rather than a
coincidence. `SUM_CAUCHY_BELOW_SQUARE` and `SUM_SQUARE_BELOW_CAUCHY` bracket the Cauchy partial
sums between `Sum a n * Sum b n` and the same read at `n + n`, and a bracket at every index
between two sequences whose limits are known is an order argument; the textbook proof is an
epsilon estimate with a split at `n / 2` in it, and there is no division anywhere here and
`NUM_DIV` is not reached. The signed case adds one identity and one squeeze, and the squeeze is
the only epsilon under either theorem.

`Series.SUM_CAUCHY_GAP` is the fact to read first and the reason there are two theorems rather
than one proof twice. It says `A_n * B_n - D_n = Sum (\i. a i * (B_n - B (n - i))) n` and asks
**nothing** of the terms, so it holds of signed series exactly as of non-negative ones: written
once at `a, b` and once at the magnitudes it gives two sums that compare termwise, and the
comparison is `ABS_MUL` with `SUM_TAIL_ABS` under it.

Three lemmas were written for that comparison and each is published on its own. `SUM_ABS` is the
triangle inequality at a finite sum, which nothing had consumed and so nothing had written;
`SUM_TAIL_ABS` is the same on a **stretch** rather than a prefix, which is `SUM_REINDEX` on both
sides of `SUM_ABS` and no induction, the lemma that looked missing having been in the library all
along; and `CONVERGES_TO_ZERO` is the squeeze at zero. All three live in `Limit` rather than in
`Magnitude` or `Series`, and the reason is the chain: `abs` belongs to the first, `Sum` to the
second, `Magnitude` is built **above** `Series` and is handed none of it, so this is the lowest
link that can write the two names in one statement.

**The exponential's series is absolutely convergent at every real since 2026-09-21**, which is
`Transcendental.EXP_ABSOLUTE` and is what the Cauchy product asks of both its arguments.
`EXP_ONE_ABOVE_TWO` did not buy it: that one dominates `1 / i!` by `2 * (1/2)^i`, and the
dominating series is the one for `x = 1` and for no other.

**The comparison test is not what proves it, and that is a measurement rather than a
preference.** `SUM_COMPARISON` asks for domination at **every** index, and a uniform geometric
dominator for an arbitrary `x` wants `(2 * abs x)^i <= C * i!`, a fact about `num` this
repository does not have; its base-two case, `Coding.NUM_POW_LE_FACT`, is two hundred and
twenty-seven lines and the general one wants a split at `N` with a monotonicity of the power in
its exponent on top. What is used instead is `MONOTONE_CONVERGES` on the partial sums, with the
bound got by **splitting** the series: `Peano.NUM_CEIL_LE` gives `M` with `2 * abs x <=
real_of_num M`, everything past `M` is under a geometric series, and everything before it is one
number. `Series.SUM_REINDEX` is what does the splitting. `TranscendentalSpec` asserts both
halves of that with `Derivation.restingOn`, including that `EXP_ONE_ABOVE_TWO` **does** rest on
the comparison test, so the absence in the other is a choice and not an accident.

Two lemmas were written under it, both published. `EXP_TERM_HALVES` is where the convergence is
decided: past the index where `2 * abs x` is reached each term is at most half the one before
it. `EXP_TAIL_GEOMETRIC` is that iterated. Three things owe a condition in the first and all
three are discharged: the two cancellations at `NUM_FACT i` and `NUM_FACT (SUC i)`, and
`Field`'s `inv f = r * inv (f * r)`.

**`exp (x + y) = exp x * exp y` is proved, since 2026-09-21**, which is the first entry on
`docs/adr/0017`'s list of what the series owe. What stood in front of it was never analysis: the
Cauchy product, then `EXP_ABSOLUTE`, then the identification of the convolution.

`Transcendental.EXP_CONVOLUTION` is that identification and it is where the arithmetic is: the
convolution of `x^i / i!` and `y^j / j!` **is** `(x + y)^k / k!`. It is `Series.POWER_BINOMIAL`
scaled by `inv (k!)` and compared termwise with `SUM_CONGRUENCE_BELOW`, and what it waited on is
`Coding.NUM_CHOOSE_FACTORIAL`: the binomial theorem's coefficient is a `NUM_CHOOSE` and nothing
in the library related that to a factorial. That identity is **written additively**,
`C (i + j) i * (i! * j!) = (i + j)!`, so it holds at every pair with nothing assumed and no
`NUM_SUB` anywhere; two ordinary inductions and no strong one, with `Peano.NUM_CHOOSE_ALL` as
the edge the recurrence cannot reach.

**Nothing in the chain is divided, and that is the decision rather than a style.** The termwise
step is `MUL_INV_COMBINE`, stated over nine real **variables**: both sides are multiplied by
`k!`, each collapses by cancelling its own reciprocals, and the division back is one more
cancellation. Turning `C k u * inv (k!)` into `inv (u!) * inv ((k-u)!)` instead would need the
coefficient to be non-zero, which is a positivity fact about `NUM_CHOOSE` this repository does
not have and would have to prove.

What the addition theorem does **not** say is what `exp x` is. Four existentials are opened in
it and none of them is a number this repository computes, which is the shape every fact about
these constants has.

**And what it buys immediately is the hyperbolic pair, which `docs/adr/0017` decided for.**
`EXP_NEGATE` is `exp x * exp (0 - x) = 1`, the addition theorem at `(x, 0 - x)` with `Ring`
collapsing the argument; it is written as a product and not as `exp (0 - x) = inv (exp x)`,
which is the same fact and would owe `~(exp x = 0)`. From it `COSH_SQUARED` is two lines:
`cosh x + sinh x` is `exp x` and `cosh x - sinh x` is `exp (0 - x)`, so their product is one and
`Ring` says that product is the difference of the squares. Those two facts landed on 2026-09-15
and had nothing to spend until the addition theorem arrived, which is what that record chose the
sum and the difference over two series for.

**The trigonometric identity is `Transcendental.SIN_COS_SQUARED`, since 2026-09-24**, and it is
not the hyperbolic one with three symbols changed: `sin` and `cos` are their own series and meet
`exp` only through a square root of minus one, which this development has no type for. So it is
a second pair of Cauchy products, the cosine's series with itself and the sine's with itself, and
what joins them is `EXP_CONVOLUTION` at `(x, 0 - x)`, which is `0^N / N!`, split by parity with
`Series.SUM_EVEN_ODD`: its even places are the cosine's product term at `m + 1` and its odd places
the sine's at `m`, so the two cancel **one index apart** and `Limit.CONVERGES_SHIFT` is what makes
that a statement about the limits. `Trigonometric.scala` is the derivation and its docstring the
argument. It costs exactly what `EXP_ADD` costs and does not rest on it, which `TranscendentalSpec`
asserts both ways.

**Continuity at a point and the intermediate value theorem are `Continuity`, a link since
2026-09-24, and the theorem is the fourth thing `COMPLETENESS` buys.** `continuous f x` is the
epsilon-delta statement written out, the way `converges` is the epsilon-N one, and
`INTERMEDIATE_VALUE` is `a <= b`, `f` continuous on `[a, b]` and `f a <= y <= f b` giving an `x` in
`[a, b]` with `f x = y`. The argument is `Root`'s: the least upper bound `s` of the points where `f`
is at most `y` has `f s` neither below `y` nor above it, and the one step that moves "a little"
moves by `min (d / 2)` of the gap, which `Linarith` decides because `d / 2` is a rational
coefficient to it. One constant, no axiom; `ContinuitySpec` asserts that the theorem reaches
`COMPLETENESS` and past the reals' sixteen exactly the choice `abs` is defined by, and keeps it from
being vacuous both ways: it is detached at the identity on `[0, 1]`, a step is shown not continuous
at zero, and the same step refutes the statement with its continuity hypothesis dropped.

**The extreme value theorem is in `Continuity` too, since 2026-09-25, and it is one lemma used
twice rather than two supremum arguments.** `INTERVAL_GLUING` says a property `P u v` of intervals
that glues (`P u v` and `P v w` give `P u w`) and holds on every short enough interval around each
point of `[a, b]` holds on `[a, b]`; `CONTINUOUS_BOUNDED` is it at "bounded above", and
`CONTINUOUS_ATTAINS_MAX` is it at "some positive gap under the supremum of the values", which is how
the maximum is reached **without** the continuity of a reciprocal, the textbook's second step and a
fact this repository does not have. `CONTINUOUS_ATTAINS_MIN` is the maximum of `\y. 0 - f y`, through
`CONTINUOUS_NEG`, the one fact about combining continuous functions it needed. `ExtremeValue.scala`
is the derivation. `ContinuitySpec` asserts all four reach exactly the reals' sixteen and the choice,
that the two attainments rest on the gluing and on the negation rather than on some other route,
detaches both at the identity on `[0, 1]`, refutes the maximum without its continuity hypothesis at
`COND (y < 1) y 0`, and refutes the gluing without its gluing hypothesis at "shorter than one".

**Uniform continuity is the gluing's third use, `CONTINUOUS_UNIFORM`, since 2026-09-25**: continuous
on `[a, b]` gives one radius per tolerance for every pair of points of it, Heine and Cantor's
theorem. What glues is **not** "one radius serves on `[u, v]`", whose pairs straddling the joint
neither half covers, but "one radius serves every point of `[u, v]` against every point at all",
which glues at the smaller radius. It costs what the extreme value theorem costs, and
`ContinuitySpec` refutes it without continuity at the step `COND (0 < y) 1 0` on `[0, 1]`.

**`ln` has its first facts, and they are `Logarithm`, a link since 2026-09-24 that declares
nothing.** `EXP_LN` and `LN_EXP` are the two compositions, `LN_ONE` and `LN_MUL` follow by
injectivity, and what they rest on is `EXP_ONTO`, the intermediate value theorem at the exponential.
Its hypotheses are the rest of the file: `EXP_CONTINUOUS`, from one estimate,
`abs (exp h - 1) <= 2 * abs h` for `abs h <= 1/2`, carried by the addition theorem; and a value on
each side of every positive number, from `1 + x <= exp x`. **The estimate needed no factorial
dominated**, which is the thing to know before reaching for `EXP_ONE_ABOVE_TWO`'s route: at a ratio
of at most a half, `t^i / i! <= t^i` because `i! >= 1`, and the geometric series does the rest.
`LogarithmSpec` refutes the estimate without its radius at `h = 8`, where `exp 8 >= 81`.

**The derivative and Rolle's theorem are `Derivative`, a link since 2026-09-25, and Rolle is the
first thing to spend the extreme value theorem.** `derivative f x m` is written with no quotient:
`abs (f (x + h) - f x - m * h) < e * abs h` for `0 < abs h < d`, which is the difference quotient
multiplied through by `abs h` and keeps every goal of the derivation inside what `Linarith`
decides. `DERIVATIVE_INTERIOR_MAX` is Fermat's lemma, by `LT_TOTAL` at the slope and a step of
`min (d / 2)` of the gap, the step the intermediate value theorem takes; the minimum is the maximum
at `\y. 0 - f y` through `DERIVATIVE_NEG`; and `ROLLE` takes both extremes from the extreme value
theorem and, when neither is strictly inside, finds `f` level. One constant, no axiom, and Rolle
costs exactly what the extreme value theorem costs, which `DerivativeSpec` asserts as an equality.
**The mean value theorem is `MEAN_VALUE`, the same day**, and it is Rolle at
`(b - a) * f y - (f b - f a) * y`, stated with no quotient: some interior `c` and slope `m` with
`f b - f a = m * (b - a)`. What stood in front of it was three facts and not analysis:
`CONTINUOUS_LINEAR`, `DERIVATIVE_LINEAR` and `DERIVATIVE_UNIQUE`. The two linearities give each
term half of the tolerance through a reciprocal of `2 * (abs p + 1)`, `Root`'s arrangement, so no
goal has a quotient in it; the mean value theorem costs what Rolle costs. **The product rule,
`DERIVATIVE_PRODUCT`, landed after it**, with `DERIVATIVE_CONTINUOUS` under it: the error splits
into three terms, each held under a quarter of `e * abs h`, and the one substitution inside a
product is done by congruence, because `Linarith` would have to multiply an equation by a factor
of unknown sign to do it and does not. **And the chain rule, `DERIVATIVE_CHAIN`**, with no
hypothesis that `g (x + h)` differs from `g x`: the error of `f` at the increment `k` is bounded in
both cases, by the derivative when `k` is not zero and because it is zero when `k` is, which is
the case the textbook's quotient cannot reach and `DerivativeSpec` detaches at a constant `g`.
**The exponential is its own derivative, `DERIVATIVE_EXP`, the same day**, and what it waited on is
one estimate rather than a rule: the addition theorem turns the error into
`exp x * (exp h - 1 - h)`, and `Logarithm.EXP_NEAR_LINE` puts the bracket under `h * h` for
`abs h <= 1 / 2`. That estimate is `EXP_NEAR_ONE` one order higher, the tail after two terms under
`EXP_TAIL_GEOMETRIC` at a ratio of a half, and it covers both signs of `h` in one argument where
the first-order one went through the reflection. It is the one fact of `Derivative` that spends a
series, so it reaches `COMPLETENESS`, the naturals' axioms and eta, all nineteen of the chain, and
`DerivativeSpec` asserts it costs exactly what the estimate costs and what the addition theorem costs.
**And the sign of a derivative on an interval, the same day**: `DERIVATIVE_ZERO_CONSTANT`,
`DERIVATIVE_NONNEG_MONOTONE` and `DERIVATIVE_POS_LT_MONOTONE`, the mean value theorem between two
points with the slope it finds carried by `DERIVATIVE_UNIQUE` to the one the hypothesis names. The
hypothesis states the derivative and its sign in one existential, so it asks no second statement
of differentiability; the three cost what the mean value theorem costs.

**Every interval theorem has a textbook form since 2026-09-25, stated with continuity relative to
`[a, b]`.** `continuous` is two-sided, so "`continuous f x` for `a <= x <= b`" asks, at `a` and at
`b`, for continuity from outside the interval as well, which no textbook does, and nothing said so
until card 6257d0da. `continuous_within f a b x` is the relative notion, and one lemma carries
every theorem across: `CONTINUOUS_EXTENSION`, that `f` extended by its value at the nearer end is
continuous everywhere when `f` is continuous relative to the interval. Each `_WITHIN` form of the
intermediate value theorem, the bound, the two extremes, uniform continuity, Rolle, the mean value
theorem and the three facts about a derivative's sign is the two-sided one at the extension, read
back through `CONTINUOUS_EXTENSION_AGREES`; `DERIVATIVE_LOCAL`, that a derivative is a fact about
the points near it, carries the derivatives. Each costs what its two-sided form costs, and
`ContinuitySpec` detaches `INTERMEDIATE_VALUE_WITHIN` at a step on `[-1, 0]` that it also proves
not continuous at `0`, so the textbook form is not a renaming. The fundamental theorem is not
among them: its hypothesis at the ends is a one-sided **derivative**, which a constant extension
cannot carry, and it got its textbook form another way, two paragraphs down.

**The integral is `Integral`, a link since 2026-09-25, and it is the gauge integral rather than
Riemann's.** `docs/adr/0049` is the decision and what it rejects is Darboux, which wanted a supremum
per piece and the common refinement of two partitions, neither of which is integration.
`fine_sum f g u v s` says `s` is the sum of `f` over a division of `[u, v]` fine for the gauge `g`,
and it is `INDUCTIVE`'s closure of two rules over the triple `PAIR u (PAIR v s)`: one piece with
its tag, and two adjacent divisions joined. There is no sequence of points anywhere in it.
`FINE_SUM_EXISTS` is Cousin's lemma, and it is `INTERVAL_GLUING` at "some fine sum exists";
`has_integral` is the epsilon-gauge statement written out and `integral` is `select` over it,
pinned by `HAS_INTEGRAL_UNIQUE`, whose one division fine for two gauges is taken at their pointwise
minimum. **`INTEGRAL_DERIVATIVE` is the fundamental theorem with no integrability hypothesis**: if
`F` has derivative `f x` at every point of `[a, b]`, then `integral f a b = F b - F a`. The gauge at
`x` is a radius the derivative gives, chosen by `select`, and the bound over a division is an
induction over the relation from the straddle inequality on one piece. Three constants, no axiom.

**The figure worth carrying is where `COMPLETENESS` enters.** `HAS_INTEGRAL_DERIVATIVE`, the theorem
stated with `has_integral`, spends fifteen of the sixteen and the choice and not the supremum,
because every fine sum being close needs no division to exist. Cousin's lemma is where the supremum
is spent, and so uniqueness and the value `integral` spend it. `IntegralSpec` asserts both as
equalities, and keeps the definition from being empty four ways: Cousin detached at a constant
gauge, the theorem detached at `y * y` on `[0, 1]`, a wrong value refused, and uniqueness refuted
without `a <= b` on `[1, 0]`, where there are no fine sums and every number is an integral.

**The integral is linear since 2026-09-26.** `Integral.FINE_SUM_LINEAR` says a fine sum of
`\x. p * f x + q * g x` is `p * s1 + q * s2` for fine sums of `f` and of `g` over the same division,
an induction over the two rules; `HAS_INTEGRAL_LINEAR` takes each function's gauge at its share of
the tolerance and their pointwise minimum, as uniqueness does; `INTEGRAL_LINEAR` names the value.
The first two cost what the fundamental theorem as `has_integral` costs and not `COMPLETENESS`,
being about the sums there are; the value goes through uniqueness and so through Cousin.

**The fundamental theorem has its textbook form too, since 2026-09-25**:
`HAS_INTEGRAL_DERIVATIVE_WITHIN` and `INTEGRAL_DERIVATIVE_WITHIN` ask for
`derivative_within F a b x (f x)` at every point of `[a, b]`, the derivative relative to the
interval, one-sided at the two ends and blind to `F` outside. It needed no extension of `F`, though
the card that asked for it had planned an affine one: the argument reads `F` only at the two ends
of a piece, and the invariant over a division already keeps both inside `[a, b]`, so the relative
derivative is enough as it stands. The two-sided theorems are derived from these through
`DERIVATIVE_WITHIN_OF_DERIVATIVE`, which costs no axiom, and so cost the same.
`DERIVATIVE_WITHIN_INTERIOR` says the relative derivative is the derivative strictly inside. `abs`
on `[0, 1]` separates the two notions: `IntegralSpec` detaches the textbook form there and refutes
the two-sided form's hypothesis at `0`, and `DerivativeSpec` refutes the interior fact at the same
point with its `a < x` dropped.

**A continuous function has an integral, `CONTINUOUS_HAS_INTEGRAL`, since 2026-09-25**, and
`CONTINUOUS_INTEGRAL` says `integral` names it. `Integrability.scala` is the derivation and it never
compares two divisions directly: a Cauchy criterion, "some gauge keeps any two fine sums over
`[u, w]` within `e * (w - u)`", glues through `INTERVAL_GLUING`, because a gauge at most
`abs (x - v)` away from the joint `v` forces every piece containing `v` to be tagged `v`, and such a
piece splits there exactly. The integral is then one supremum, of `t - e * (b - a)` over good gauges
and their fine sums, two of which are compared through a third that Cousin supplies. It costs the
gluing's price; `IntegralSpec` detaches it at the constant one and joins it to the fundamental
theorem's value there. No control refutes it without continuity: Dirichlet's function is gauge
integrable, so a counterexample has to be unbounded, and that is an argument of its own.

**The second half of the fundamental theorem is `DERIVATIVE_WITHIN_INTEGRAL`, since 2026-09-26**: for
`f` continuous on `[a, b]`, `\y. integral f a y` has derivative `f x` relative to `[a, b]` at every
point of it, and `DERIVATIVE_INTEGRAL` is the same strictly inside as a two-sided derivative, through
`DERIVATIVE_WITHIN_INTERIOR`. What it needed first was `HAS_INTEGRAL_JOIN`, that integrals add over
adjacent intervals, and that is the joint gauge of the existence again: it splits every fine sum at
the join exactly, so additivity costs no supremum at all, fifteen of the reals' axioms and the
choice. The increment is then read by additivity and uniqueness as the integral over the interval
between `x` and `x + h`, on either side, and a sum fine for both that integral's gauge and the
radius continuity gives puts it within half the tolerance of `f x * h`. In the relative form
`a <= x` and `x <= b` carry no weight: outside the interval no small increment stays in it, so the
relative derivative holds there at any slope.

**The sine and the cosine are differentiable since the same day, and what stood in front of that was
the addition formulas.** `Transcendental.COS_ADD` and `SIN_ADD` are `SIN_COS_SQUARED`'s argument at a
second point: `EXP_CONVOLUTION` at `(x, y)` rather than at `(x, 0 - x)`, split by parity, whose even
and odd places are the terms of the Cauchy products of the two series at `x` against the two at
`y`, with the cosine's one index apart as in the square and the sine's not shifted. The general
point is simpler than the special one: at `0 - x` a partner's power had to be carried back to `x`
with `POWER_NEG_DOUBLE`, and at `y` it is the same atom on both sides, which `TranscendentalSpec`
asserts by checking that neither formula rests on it. `Logarithm.COS_NEAR_ONE` and `SIN_NEAR_LINE`
put `cos h - 1` and `sin h - h` under `h * h` for `abs h <= 1 / 2`, their terms being the
exponential's at the even and the odd places under `EXP_TAIL_BOUND`; `Derivative.DERIVATIVE_SIN` and
`DERIVATIVE_COS` follow, with `SIN_COS_SQUARED` keeping the coefficients at most one. The radius in
the two estimates is the proof's and not the statement's: `1 - cos h <= h * h / 2` holds everywhere,
so nothing refutes them without it, and what `LogarithmSpec` refutes instead is `COS_ADD` with the
other sign, at one half, through `sin (1 / 2) >= 1 / 4`.

**The logarithm's slope is `DERIVATIVE_LN`, since 2026-09-26**: `0 < x ==> derivative ln x (inv x)`.
With `t = h * inv x` and `u = ln (1 + t)`, `LN_MUL` makes the error exactly `u - t`; the exponential's
strict monotonicity keeps `abs u <= 1 / 2` once `abs t <= 1 / 4`, and `EXP_NEAR_LINE` at `u` does the
rest. It costs what `DERIVATIVE_EXP` costs. **It is a derivation for this inverse and not a theorem
about inverses**: the general one wants the inverse continuous at the point, which nothing states
for `ln`, and `ln` is the only inverse the library holds. The hypothesis `0 < x` is not shown
necessary and cannot be: at a point that is not positive `ln` is a choice nothing constrains.

**The square root is `Root`, a link since 2026-09-24, and it is the third thing `COMPLETENESS`
buys.** `sqrt x` is `select (\y. 0 <= y /\ y * y = x)`, and `SQRT_EXISTS` is what makes the choice
say something: the least upper bound `s` of the non-negative numbers whose square is at most `x`
squares to `x`, because below it `s + e` is still in the set and above it `s - e` already bounds
it. One constant, no axiom, and the existence rests on the reals alone: `RootSpec` asserts that it
reaches `COMPLETENESS` and nothing the chain adds, and that every fact about the constant spends one
choice more and nothing else. It spends the supremum inline too, as `MONOTONE_CONVERGES` does, and
so does `Continuity` after it: four consumers now, each with the least upper bound written out.

The derivation has no quotient in it and no classical step, and that is the shape to copy. Each `e`
is `d * inv c` with `c` a sum already known positive, the only fact about the reciprocal it uses is
`MUL_INVERSE` at `c` turned into `e * c = d`, and the two absurd branches of the trichotomy leave by
ex falso. It also found a limit of `Linarith` worth knowing before reaching for it: from `0 <= a`,
`0 <= b` and two equal squares it settles `a <= b` and refuses `a = b`, so `SQRT_UNIQUE` is two
inequalities and an antisymmetry. `Root.scala` says where in `Linarith` the difference seems to
come from, and that the reading is not verified.

`LimitSpec` detaches **both** Cauchy theorems at the geometric series on both sides and asserts
`hypotheses` empty, because an implication with four antecedents that nobody can discharge is a
theorem that says nothing. It asserts separately, by `Derivation.restingOn`, which published
facts are inside each derivation, since a theorem proved the textbook way would read the same
word for word.

**A quotient with a symbolic denominator is outside every procedure here, and that decided the
shape of the whole derivation.** `Linarith` refuses `x / y` by name, saying that cancelling a
symbolic denominator needs it to be non-zero and is `Field`'s to assume. So no goal in that proof
carries one: the reciprocal enters as a variable with the hypothesis `f * v = 1`, which is
`MUL_INVERSE` at a denominator already known positive, and each step is a schematic implication
over real variables that is specialised afterwards. It is the shape to copy for any bound on a
series whose terms are quotients.

Three things in those derivations were harder than they look and each is recorded where it happens.
Halving a tolerance is `Linarith`'s, because a numeral denominator is a rational coefficient to it
and `0 < e ==> 0 < e / 2` is inside the fragment it decides. Putting two indices together is
`Peano.NUM_LE_ADD` and not a maximum, because `num` has none. And the rewriter is given **two**
equation sets rather than one: `NUM_ONE_SUC` rewrites the `1` inside a bit encoding, so with it in
the set the `2` in the cosine's exponent becomes `NUM_BIT0 (SUC ZERO)` and stops matching a lemma
proved about `Power 0 2`, which is the refusal that produced the split.

**The integers are `Integer`, a link since 2026-09-18, and they arrive as a prerequisite rather
than as stage four of the construction.** `docs/adr/0033` is the decision and `docs/adr/0016` is
what it extends. A pair of naturals `(a, b)` stands for `a - b`, two pairs stand for the same
integer when `a + d = c + b`, and `int` is `Quotient.define` applied to that relation: the first
real consumer of the builder that record asked for, which was validated on a toy quotient before
anything was built through it. Written additively on purpose, since `num`'s subtraction is
truncated and the reading with a `NUM_SUB` in it is not an equivalence. **It costs no axiom beyond
the carrier's**: choice, eta and infinity, which the pair and the naturals already cost, and
`IntegerSpec` asserts that as an equality rather than as a ceiling and separately that none of the
sixteen is among them.

What it is for is that neither existing divisibility can state the condition two open
formalisations need. `Divisibility` is over the reals, where `DIVIDES_NONZERO` makes every
non-zero element divide everything, so the hypothesis is discharged **vacuously**; and
`NUM_DIVIDES` is over `num`, which has no negative numbers. `INT_DIVIDES` is the one that can, and
`INT_DIVIDES_LINEAR` is the step a lattice argument is made of.

**The non-collapse guard is a theorem here and is not one in `QuotientSpec`**, which says in as
many words that it cannot carry it: refuting collapse there needs `~(NUM_CONG 2 2 3)` and nothing
in this repository derives it. `num` has `Successor.distinct`, so
`~(INT_OF_PAIR (PAIR 0 0) = INT_OF_PAIR (PAIR 1 0))` is derived, and the injectivity of
`INT_OF_NUM` says the same for every pair of naturals. A one-point `int` passes every other
assertion in the file.

**The operations keep a prefix spelling and that is a decision.** `docs/adr/0018` lets a symbol
stand for more than one constant and `+`, `*`, `<` and `<=` already stand for two; a third
candidate gives every existing statement a new way of being ambiguous, and 135 statements moved
the last time a type joined the overloading. So it is `INT_ADD a b`, for the reason `num`'s
truncated subtraction keeps a prefix form for a different one.

**The order is the one construct the quotient builder does not reach**, and what it needed is worth
knowing before opening the file. `Quotient` lifts a unary operation, a binary one and a predicate
of **one** argument; a relation of two quotient arguments is none of the three, since
`liftBinary`'s obligation relates the two results and so needs them in the carrier. So `INT_LE` is
defined through the chosen representatives directly, and `INT_LE_PAIRS` is the fact that makes
that definition usable. Its respectfulness lemma is the only obligation in the development that is
an equation between **propositions**: two related pairs have to give the same order, in both
directions, so it is `Kernel.deductAntisym` over two implications rather than a rearrangement, and
`Semiring` cannot be handed the conclusion because the conclusion is an order.

**The bridge into the reals is `Inclusion`, a link since 2026-09-18, and it is the one piece of the
integers that mentions a real.** `real_of_int`, a ring homomorphism, the triangle
`real_of_int (INT_OF_NUM n) = real_of_num n`, injectivity, and the order map. One constant, no axiom, and it is a
development of its own rather than a section of `Integer.scala` because that file says of itself
that nothing in it reaches for a real, and `docs/adr/0033` rests phase 5's move of it below `Real`
on the sentence being true. `Embedding.scala` is the precedent one type down and `docs/adr/0016`
drew that line.

**What it cost the quotient builder is not what the card predicted, and the prediction is worth
reading before the answer.** `Quotient.scala` said it did not lift a function whose result is not
quotiented and named the integers as the consumer that did not need one; the card predicted that
`liftPredicate` would in fact lift the bridge unchanged, since nothing in it reads the result type.
That held. What was missing is a different thing: a lift defines its constant into the quotient's
**own** theory, and the integers define five more constants after their three lifts, so
`Integer.quotient.theory` carried 140 constants where `Integer.theory` carried 145 on the day the
bridge landed, and `real_of_int INT_ZERO = 0` could not be stated there at all. `Quotient.over`
re-bases a quotient onto a theory extending it, checked by `Logic.over`, and that is the whole of
the addition.

**And it is where the axiom accounting divides.** `IntegerSpec` asserts that no fact of that
development reaches any of the sixteen; every fact of this one does, because every one of them is
decided over the field. `InclusionSpec` asserts both halves in one test, because a reading that
answered the same for everything would pass either alone.

**The order map is `INT_REAL_LE`, landed the same day, and it is the one fact here of a different
shape.** `INT_LE a b = (real_of_int a <= real_of_int b)`: an equation between **propositions**,
where the others are equations between reals, so the route they share does not reach it — its last
step is `Ring`, which has nothing to say about an order. It is two implications joined by
`Kernel.deductAntisym`, each crossing on one fact about the embedding and the order.

**What it cost is the half to read, because it is where the work was.** The library held
`NUM_REAL_LE`, which carries a bound on `num` **out** to the reals, and held no way back, so the
right-to-left half of the biconditional had nothing to cross on: the fact was unstatable for that
reason rather than unwritten. `Peano.NUM_REAL_LE_BACK` is the converse and its route is
`NUM_LT_TOTAL` rather than the contraposition a reader reaches for, because turning
`~(NUM_LE m n) ==> NUM_LT n m` around is a classical step the derivation would then owe, where
trichotomy puts the three cases on the table before anything is negated. Two of the three cases are
one line each; the third is `NUM_REAL_LT` spending the **integrality**, the same thing
`NUM_REAL_INJECTIVE` spends.

**`InclusionSpec` spends the new fact at a pair rather than only reading it**, which is the guard
the form assertions cannot be: `INT_LE INT_ZERO INT_ONE` comes out of `0 <= 1` on the reals and
`INT_LE INT_ONE INT_ZERO` is **refused**, both with nothing assumed. The negative is the half that
matters, since `Integer`'s four order facts — reflexivity, transitivity, antisymmetry, totality —
are all satisfied by a one-point `int`.

**The divisibility is separated from the field's since 2026-09-19, and the separation cost none of
what was predicted.** `~(INT_DIVIDES 2 1)` is the sharpest thing that separates them,
`docs/adr/0033` listed it as missing and said it wanted the discreteness of the order, and it
wanted no such thing:
`INT_DIVIDES_OF_NUM` is the embedding answering alike on both sides, one biconditional rather than
the implication and its converse that record listed apart, and under it the refusal is
`Modular.NUM_DIVIDES_ONE` at two numerals. The witness of a divisibility over `int` is an integer,
so reading it back as a natural is what wants a sign argument; `INT_CASES` writes it as a pair
instead and the equation between classes becomes one equation between naturals, with no case split
anywhere. `IntegerSpec` walks the refusal and asserts no fact of `INT_LE` is in its derivation, so
the corrected record is a check rather than this sentence. What is left of that record's list of
what is missing is nothing: the paragraph below is where the rationals are, which it never listed.
It is still the kind of list nothing goes red over, and the reason those two entries were built is
that somebody gave them a card, which the third already had and they did not.

**Identities of a commutative ring are decided by one builder since 2026-09-25, and the rationals
have their operations.** `CommutativeRing` takes the constants and the axioms and derives every
other rule a normaliser needs; `Semiring` is its `num` instance, with normal forms unchanged, and
`Integer.ring` its `int` instance. Angelo decided for the generalisation over deriving the
rationals' obligations by hand, and `docs/adr/0046` is the record. `CommutativeRing.consequence`
closes an equation that follows from premises by substitution given the coefficient of each, which
is the shape of every respectfulness obligation: `Fraction` lifts `RAT_ADD`, `RAT_NEG` and `RAT_MUL`
through it, with `RAT_DENOMINATOR` reading the stored index `d * e + d + e` back as `SUC d * SUC e`.
**The order is the thing to know before touching it**: compared under the negations, by size inside
the recursion with a negation adding no size, and by the number of negations last; counting the
negation's node sent `-m` to the end of a sum and the rationals' first obligation was refused, which
`tools/verify/perturb-commutative-ring.sh` fires. **`rat` is an ordered field since the same day**:
`RAT_INV` is defined with the value at zero written by its conditional, `RAT_MUL_INV` holds off zero,
and `RAT_LE_ADD` and `RAT_LE_MUL` tie the order to the operations. The existence of an inverse
needed the sign of the numerator, which the pair holds as an integer, and `INT_OF_NUM_CASES` is that
split; `tools/verify/perturb-rational-field.sh` fires the zero branch and the sign of the witness.

**And Archimedean and dense, the same day**, which is what the reals as cuts ask of the rationals
beyond the field. `RAT_LT x y` is defined as `~(RAT_LE y x)` and `RAT_OF_NUM n` as the class of
`(INT_OF_NUM n, 0)`; `RAT_ARCHIMEDES` bounds every rational by a natural, `RAT_ARCHIMEDES_INV` is
the form a cut spends, some `1 / (n + 1)` under every positive tolerance, and `RAT_DENSE` puts the
midpoint between two rationals. `Density` is the derivation, and the thing to know before opening it
is that it argues **on classes**: `CommutativeRing` instantiated at the laws of `rat` decides every
identity, and `consequence` one that holds under a premise such as `2 * RAT_INV 2 = 1`. Only
Archimedes and the two values of `RAT_OF_NUM` open a representative, and Archimedes is where the
numerator's sign is spent. `tools/verify/perturb-rational-density.sh` fires the midpoint and the
bound.

**The reals as cuts have started, and the first thing built is the axiom worth the most.** `Cut`,
beside the chain as `Fraction` is, carves `cut` out of `rat -> bool` with `IS_CUT`: a lower cut
holds something, not everything, is closed downwards and has no greatest element, the last clause
being `RAT_DENSE`. The order is inclusion, and `CUT_COMPLETE` is `COMPLETENESS`, the sixteenth axiom
of `Real.scala`, stated word for word over `cut` and **proved**: the least upper bound is the union.
`docs/adr/0052` is the route, lower cuts with the sign handled at multiplication, and why the
positive cone first lost now that `rat` exists. Addition and negation followed the same day:
`CUT_ADD` holds `r` when some `p` in `x` leaves `r - p` in `y`, with its commutativity,
associativity, zero, the order it carries and the embedding of `RAT_ADD`; `CUT_NEG x` holds `p` when
some `r > 0` leaves `-p - r` outside `x`, and `CUT_ADD_NEG` is `x + -x = 0`, the one argument of the
two where `RAT_ARCHIMEDES` is spent, which `CutSpec` asserts both ways. What is not here is
multiplication and the inverse, and after them the sixteen as theorems under their own names.
`tools/verify/perturb-cuts.sh` fires the union, the embedding and the step of the inverse.

`NUM_GCD` and `NUM_DIV` are both chosen rather than calculated, and since 2026-09-25 each has a
computing counterpart proved equal to it: `EuclidAlgorithm` defines `NUM_EUCLID_GCD` and
`NUM_EUCLID_DIV` by `WellFounded`'s recursion along a measure, beside the chain, and
`NUM_EUCLID_GCD_IS_GCD` and `NUM_EUCLID_DIV_IS_DIV` are the two equalities, off both zero and off a
zero divisor. What is not done is wiring that development into the chain, which is why `Ask` and
`Find` do not reach either. The reals are still axiomatised: `docs/adr/0004` records
why, and why the same reasoning does not extend to the naturals, and `docs/adr/0007` orders their
construction, which `docs/adr/0006` is the rule that unlocked.

**A theory of a domain that is not mathematics is a theory like any other, and one exists as a
test rather than as a description.** `DomainTheorySpec` declares a type and five constants nothing
else has, asserts as axioms the four sentences of a release gate (a change ships on two reviews, or
on one review and a green pipeline, or as a revert, and on no other ground), and derives a claim
about them twice, by hand and through a procedure, which is the comparison the paragraph after this
one is about. The criterion is **invented**, and until 2026-09-15 it was not: it was the
admission criterion of the practice this repository is developed under, which made a fragment of a
private document the subject of a public test. The accounting does not depend on whose rule it is,
because what a derivation spends is fixed by the logical shape; what was given up with the real one
is the claim that the domain is in daily use, and the file says so. What it is for is the
accounting rather than the proof: the conclusion rests on **one** of the four axioms asserted, and
on **no foundational axiom at all**, neither choice nor infinity nor any of the reals. Which of
the assumptions a conclusion actually spends is the question worth asking about a claim of the
world, and `Derivation.axiomsOf` answers it; `Derivation.foreignTo` says which belong to the
domain and which to the foundation under it.

**A domain claim was a hand derivation and is no longer one**, and this paragraph has been repaired
twice. Until 2026-09-15 it said the derivation was the only route, in the same words as the header
of the file that had already stopped being an example of it. Until 2026-09-16 it said the route that
existed charged an axiom the hand derivation does not, which was true and was the gap rather than
the answer. `Domain.Built.settle` is the call: it specialises this domain's axioms at the subjects
the claim names, decides the propositional skeleton with the domain's constants as atoms given no
meaning, keeps only the axioms the decision needed, detaches, and reports what it spent. One line
where the derivation is forty, **same theorem, same one domain axiom, and no foundational axiom
either**.

What closed it is `Intuitionistic` in `modules/logic`, Dyckhoff's contraction-free calculus, which
decides intuitionistic propositional logic with negation included and certifies the answer out of
the derived rules alone, so it costs nothing at all. `docs/adr/0022` is the decision. `Propositional`
is still the fallback for a claim that is classically valid and no more, at the choice axiom, and
`DomainTheorySpec` exercises that route beside the other so that the agreement between the two is a
measurement rather than a remark about an empty set.

**And the fallback is taken for two different reasons, which since 2026-09-18 the answer tells
apart.** The calculus refuses a claim that is not intuitionistically valid, and it also refuses one
whose search ran out of `Intuitionistic.Fuel`; both fell to the classical route and both came back
`Settled` at one axiom, so a price the net caused was indistinguishable from a price the logic
asked for. `Domain.Verdict.CutShort` is the second of those now, and `docs/adr/0026` is the decision
with the measurement that made it worth making: the net is **reachable** here, at a length strictly
inside this method's own `Domain.Instances` bound, by a chain of modus ponens whose only difference
from a free one is its length. The figure `docs/adr/0023` rests on for the same defect at `Prove`
does not travel to this site, and that record now says so rather than being cited here.

**The accounting is what the method is for, and the obvious implementation destroys it.** Handing
every specialised axiom to the procedure and detaching all of them reaches the same theorem and
makes `Derivation.axiomsOf` report all four where the hand derivation spends one, which is what the
first run of it did. So the instances are cut down to an irredundant set first, by dropping each in
turn and deciding again without it, which is an unsatisfiable core obtained by deletion rather than
read off a refutation: `Propositional` does not publish the clauses its refutation read and the
intuitionistic calculus has no clauses at all. It costs `2n + 1` decisions and it is minimal rather
than minimum.

**A claim reaching arithmetic is settled when the caller names the fact that carries it across**,
and that is `docs/adr/0024` since 2026-09-18. What the record rejects is the repair everybody
reaches for first, an interpretation of the domain's constants: measured against the example the
work was asked for, `Attempts : job -> num` has nothing to interpret, because its result type is
already the foundation's. `Attempts j` is not an atom standing in for a number, it is a number
nobody knows, so a fact used about it must hold for all of them and nothing is approximated.
`Peano.NUM_LT_NOT_LE` specialised there is what `!j:job. Attempts j < 3 ==> ~(Abandoned j)` was
missing, and the skeleton over it is intuitionistic at **zero** axioms.

The bridge is the caller's, and since 2026-09-18 it is also something that can be **found**:
`Bridging` is a search over a library, above `Domain.Built.settle` and calling it, and
`docs/adr/0027` is the decision. It puts the lemmas about the foundation constants a claim names to
that method one at a time, reports which one carried it, and refuses where none did, naming what it
tried. What makes the report honest rather than an order of trying is the control it runs first: a
claim that settles carrying nothing but `|- T` had inert arithmetic in it and comes back with no
bridge named, because a foundation constant can sit where the decision never reads it. What it
costs is **reported**, which is the whole permission: the bridge carries the naturals' two axioms,
`Derivation.axiomsOf` walks
them, and `DomainTheorySpec` asserts the conclusion spends **exactly** what the bridge spends and
not one axiom more. That equality rather than a non-emptiness is deliberate: non-empty would pass
just as well if the decision had fallen through to `Propositional` and charged `SELECT`, which is
the trade `docs/adr/0022` exists to refuse and which a choice axiom the naturals cost anyway would
have hidden.

**A domain type is interpreted at the build, and that is `docs/adr/0028` since 2026-09-18.** A
domain that keeps a type of its own is not merely refused arithmetic: a claim needing it **cannot
be written**, because `NUM_LT c 3` at `c:cost` is a type error and not a verdict something could
lift, which `InterpretationSpec` measures. An `Interpretation` sends a type of the domain to a type
of the foundation, and then that type is not declared at all; it also sends a constant of the
domain to a **definition** rather than a declaration, so the predicate stops being an atom with
nothing inside it. Neither costs an axiom, and the second is what a claim turning on what a word
*means* was missing: a measure into `num` leaves the predicate opaque however much arithmetic is
available about the number.

What it costs a reader is a second thing to check, and the report says so: `Domain.Spending.defined`
names the interpreted constants the conclusion **rests on**, walked out of the derivation rather
than read off the statement, because the interesting case is exactly the one where the meaning was
spent on the way and is gone from what was proved. The refusal stays for the domain built without a
map, and `InterpretationSpec` keeps it non-vacuous by building **one** description both ways.

Nor does the search combine two lemmas: one that needs two facts at once is refused in those words,
since a refusal a reader takes for "out of reach" would hide the route that does settle it, which is
naming both.

Such a theory sits beside the chain and must stay there: two theories that axiomatise one name are
the case `docs/adr/0008` leaves open, and `SoundnessAttackSpec` still derives `|- F` from it.
