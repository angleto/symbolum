# Symbolum

## What this is

A computer algebra system that is also a proof assistant, in one repository, and the relationship
between the two is the whole design. The algebra side is fast and knows a lot; several of its
rewrites are valid only under hypotheses it does not record. The proof side is slow and knows
almost nothing; what it produces is certain. They are joined so that the first proposes and the
second checks, which is the arrangement `docs/adr/0003` describes.

**The thing a newcomer gets wrong:** assuming `modules/core` is trusted because it is the oldest and
largest part. It is not trusted at all. Nothing it says is believed anywhere in the proof side, and
that is deliberate: it is what lets it stay fast and heuristic.

## Running it

- **Tests:** `sbt test`. Most of the wall clock is one suite: `ReachSpec` puts miniF2F's 244
  statements to the whole tactic surface and most of **that** is the eighteen it attempts and cannot
  settle. That cost is the prover's rather than the test's, and it is tracked.

  **The number that used to be here is gone rather than corrected.** It said forty seconds, against
  eleven before the corpus landed, and by 2026-09-14 a run was taking a hundred and ten on a quiet
  machine and twelve minutes on a busy one. A wall clock depends on the machine and on what else is
  running, so unlike every other figure in this repository it cannot be generated from the code
  either: there is no source of truth for it to be read off. What the sentence was for survives
  without it, which is that the cost is concentrated in one suite and why that suite is not
  excluded. This is the third of the three repairs `Generated.scala` lists, and it records that this
  one is met most often and chosen least. It is **not** excluded here, on purpose: a corpus that runs only when
  somebody remembers to ask for it has stopped being a measurement, and the figures in
  `docs/evaluation.md` are meant to fail rather than go quietly stale.

  It was two minutes for most of 2026-09-11, and the minute and a half that went is worth a line:
  `Abduce` was running a quadratic comparison over candidates it should never have compared, which
  it reached by misreading "the satisfiability question was not settled" as "the premises hold up".
  A suite that got slower is how that was found.
- **One module:** `sbt kernel/test`, `sbt theories/test`, and so on
- **One suite:** `sbt "core/testOnly garden.xeno.symbolum.CanonicalFormSpec"`
- **Coverage, with the floors enforced:** `sbt clean coverage test coverageReport`. This one
  **skips the corpus measurements**, which `sbt test` does not: the two ask different questions, and
  `ReachSpec` exercises the same lines as the other corpus suites while costing more than the rest
  of the build put together. `build.sbt` and `garden.xeno.symbolum.tactics.Corpus` carry the argument.

  **`clean` is not optional and the gate will not tell you.** The report is built from what the
  instrumented compiler saw, so on an incremental build it covers only the files that were
  recompiled. Run twice a commit apart on 2026-09-13, the second report held **two files**:
  `theories` read 172 statements at 100.00% against 22663 at 97.56%, and the gate **passed**,
  because 100 is above the floor. Read the statement count beside the rate, and run it in a
  worktree that has never been built or after `clean`. There is no check for this, and `build.sbt`
  says why there cannot easily be one.
- **A console with the algebra loaded:** `sbt core/console`
- **Asking the prover one thing, without writing Scala:**
  `sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. x + 0 = x"`. It puts the claim to the whole
  tactic surface over the widest signature the chain assembles, so a claim about `num` is one it can
  take, and prints what `Cost` reports: the outcome, the price, the axioms, what it rests on, and
  where it fails if it fails. `|` separates two claims; the claim is **not** quoted, because `sbt`
  hands the arguments over already split and the shell's quotes are gone by then.
- **Looking for a lemma, by name or by shape:**
  `sbt "tactics/runMain garden.xeno.symbolum.tactics.Find SUM"`, or
  `sbt "tactics/runMain garden.xeno.symbolum.tactics.Find x:real + y:real = y + x"`. It puts the query to all
  three of the library's questions, the name, the constant and the shape, and prints each answer
  under its own heading including the empty ones, because a reader shown two answers to three
  questions cannot tell which was empty and which was never asked. A bare identifier reads as a
  boolean **variable** and a variable pattern matches every lemma there is, so that one is refused
  by shape rather than answered with the whole library.
- **Working on a theory interactively, in a browser:**
  `sbt "tactics/runMain garden.xeno.symbolum.tactics.Notebook"`, then open `http://127.0.0.1:8642`. A column
  of cells over one `Session`: `declare`, `define`, `assume`, `prove`, `ask`, `find`, `show`. The
  chain is built once when it starts, a few seconds, and each question after that is milliseconds.

  **A session holds exactly one theory, and that is the whole safety argument rather than a
  convenience.** The falsity `SoundnessAttackSpec` derives needs *two* theories that each declare
  one name, and a notebook whose cells re-run in any order is that caller by construction. So the
  transcript is append-only: going back to a cell discards everything after it, and a second
  `declare p` is refused by the kernel's own `AlreadyDeclared` because there is one theory to
  declare into. `assume` is in the language, because the promise here is accounting rather than
  purity: every theorem downstream of an assumption carries it, printed on the page, through
  `Derivation.foreignTo` against the chain.

  What it cannot do, named rather than left to be discovered: **no tactic spends an assumption.**
  No procedure searches over an assumed constant, and the reason is the surface's rather than the
  domain's: the tactic surface is built over the base chain, so a claim in a vocabulary the session
  added is one no procedure has a reading of. The domain-theory paragraph below is what says a
  procedure is not barred from a domain's constants in principle. So a session's own axiom reaches
  a conclusion through a hand derivation, and since `c0830ce` the command for that **is** written:
  `derive NAME : <step>`, over the `Recorder` in `modules/logic`. This said it was not written for
  the hours between that commit and 2026-09-16, which is the shape of stale reference nothing goes
  red on. What it offers is the five inferences whose arguments are names of facts the session
  already holds; the three of `DomainTheorySpec`'s that take a term or a free variable as a premise
  are absent and named absent in `Session.Surface.Inferences`, because offering one is a decision
  about elaborating a term in the middle of an inference and not this one.

  **A paste of several lines is one submission and its lines run in the order they were pasted**,
  which is how a development is replayed, and a submission names the transcript it was written
  against, so anything else driving the port is refused rather than interleaved into it. Both
  landed on 2026-09-16: until then the page fired one request per line and waited for none of them,
  so the order of a transcript was the network's rather than the writer's. It is listening on
  loopback with no authentication: a single-user tool, not a service.
- **Regenerating `docs/lemmas.md`:** `sbt "theories/runMain garden.xeno.symbolum.theories.Lemmas"`. It
  replaces what lies between the two markers and leaves the prose above them alone. `LibrarySpec`
  compares the file against the code and fails naming this command, which is the point: the document
  breaks exactly when somebody adds a lemma.
- **Regenerating the mark:** `sbt "mark/runMain garden.xeno.symbolum.mark.Mark"`. It writes **both**
  the character art in `docs/logo.md` and `docs/logo.svg`, from the description in
  `garden.xeno.symbolum.mark.Figure`, which is in radii rather than in cells. It **refuses** rather
  than writing when what it draws fails one of the three checks that document describes: that the
  operator stream covers every filled cell in reading order, that the mark is one connected region,
  and that it encloses exactly one empty one. `MarkSpec` runs the same three and compares both
  committed files against the description, failing and naming this command.

  **With a size in rows it prints instead of writing**, which is the point of the description:
  `sbt "mark/runMain garden.xeno.symbolum.mark.Mark 33"`. Not every size holds, and the ones nobody
  has measured are a question rather than a gap: twenty, twenty-three and thirty-three hold,
  twenty-six leaks its counter and forty-six seals a pocket, and `MarkSpec` asserts all five.
- **Regenerating `docs/reading-register.md`:**
  `sbt "theories/runMain garden.xeno.symbolum.theories.Register"`. The same arrangement as the lemmas, for the
  three things nothing but a reader checks: every axiom, every defined constant and every row of the
  precedence table, each with whether somebody has read it, when, and against which source.
  Everything says **NOT READ**, because nothing has been. The attestations are written by hand in
  `docs/reading-register-attestations.txt` and are folded in by the generator, so a reading survives
  the regeneration and nothing is ever recorded by editing the generated block. `RegisterSpec` fails
  when a statement has no row and names this command. It checks nothing about whether a statement is
  **right**, and the document says why a test that appeared to would be worse than none.

## Layout

Dependencies point one way, and the direction is the correctness argument rather than tidiness:

```
kernel    -> (nothing)      the trusted base
checker   -> kernel         a second reading of a proof, as text or in this process
sat       -> (nothing)      a conflict-driven solver and the refutations it produces
logic     -> kernel, sat    connectives, derived rules, rewriting, parser, printer
theories  -> logic          the naturals, the reals, numerals, arithmetic, RING, LINARITH
core      -> (nothing)      the computer algebra system, published as garden.xeno:symbolum-core
tactics   -> theories, core the lowest module that sees both halves
examples  -> tactics        runnable demonstrations of either half, not published
mark      -> (nothing)      the figure, the art and the drawing written from it, and its checks
scan      -> (nothing)      what in a source of this repository is a comment, for the gates that ask
```

`sat` depending on nothing is the same kind of statement as `kernel` depending on nothing, read from
the other end. A search is untrusted here, and a module that cannot see `kernel` cannot construct a
theorem whatever it does, which `modules/sat/src/test/.../IsolationSpec` asserts. It is worth having
as a module rather than as a file under `tactics` because that is the difference between a property
and a convention: `tactics.Consistency` makes the same promise about itself with a test that scans
its own source for the name of an inference rule, and its comment says why a runtime check was not
available to it.

`mark` is beside that graph rather than in it: nothing depends on it and it depends on nothing. It
is a module and not a file in `examples` for one reason, which is that `examples` depends on
`tactics`, and a check over two files under `docs/` that could only run after the prover compiled
would stop running on exactly the days the prover is broken.

`scan` is beside it for the same argument and is reached only at **test** scope, by `theories`,
`tactics` and `dist`. It holds the one decision about what in a source of this repository is a
comment. Six gates decided that separately until 2026-09-16, in two shapes that disagreed on three
inputs: a trailing `// note` after a call, a doc comment closed in the middle of a line, and a `//`
inside a string literal, where the text-cleaning shape deleted real code. What makes it a module
rather than a file in one of the three test scopes is the measurement: sharing along the edges that
already exist means `theories % "test->test"` on `tactics`, which puts 75 test files and 21 097
lines into the compile graph of every `tactics/testOnly` to remove two copies of one function. The
main scopes are untouched, so nothing published can see it and the trust boundary is unchanged.

`kernel` declaring no dependency is what makes the trusted base something you can point at rather
than describe, and a test in `modules/kernel/src/test` asserts it cannot see the algebra side.

`tactics` was **the only** module seeing both halves until 2026-09-13, and that sentence was worth
correcting rather than preserving: what the split enforces is that nothing **below** `tactics` sees
`core`, and `examples` is above it. It depended on `core` alone, which made it the algebra's
demonstration directory by accident of the graph, and a demonstration of the proof half had nowhere
to live. `WhatAClaimCosts` is the first one that does.

## The trusted base, exactly

Everything this system asks anyone to believe, and no one development is asked for all of it:

1. **`Kernel`, `Term`, `Type` and `Theory` in `modules/kernel/src/main`**, under 1200 lines. The
   directory also holds a printer, the refusal surface and the proof record, which are not counted
   and cannot construct a theorem, which a test checks rather than claims. `Kernel.Thm` is a class
   with a private constructor rather than an opaque type, which erases to what it wraps:
   `TrustBoundaryTwinSpec` casts the underlying pair and gets a `ClassCastException` where it used
   to get a theorem out of nothing. Ten primitive inference rules construct a theorem, and three
   theory extensions also do: defining a constant, defining a type, and asserting an axiom. Only
   the last of those adds to what has to be believed. Term constructors are `private[kernel]`, so a
   term exists only because a checking constructor built it and is well-typed by construction. Type
   constructors are not private, because naming a type proves nothing: a type entering the system
   from outside is checked by `Theory.checkType`.
2. **The sixteen axioms in `modules/theories/.../Real.scala`**, which state a complete ordered
   field. `RealSpec` asserts the theory holds exactly those and in that order.
3. **Three axioms added on 2026-09-10**: a choice operator and eta in
   `modules/logic/.../Classical.scala`, and infinity in `modules/theories/.../Natural.scala`. The
   first two are asked of the formalism rather than of a domain, and the third of a type nothing
   else interprets. `docs/adr/0007` is the record of choice and of infinity, `docs/adr/0009` of
   eta. They are what the naturals are built from, and the naturals are **defined**: the type `num`
   costs no axiom of its own. **The excluded middle is not among them**: it is derived from choice
   alone, in 841 steps, and three places in the repository said the opposite until `docs/adr/0009`
   measured it. That figure is written by hand in four documents **and asserted in all four by
   `ClassicalSpec`**, which is what makes writing it by hand safe here: the four went stale together
   once and were found by grep rather than by a test. It has moved twice, 983 to 829 when
   `Conv.refl` began sharing an atom's reflexivity, and 829 to 841 on 2026-09-16 when `Rules.mp`
   stopped accepting an antecedent differing from the implication's by a beta redex. Which of the axioms a session pays for depends on what it builds on, and
   `NaturalSpec` measures each case: sixteen over the reals alone, three over the naturals alone,
   nineteen for a development holding both, which is what `Chain.standard` assembles and `ChainSpec`
   asserts. `docs/adr/0007` decides that the reals will be constructed rather than axiomatised, so
   this count goes up before it comes down: the sixteen become theorems at the end of that work and
   what is left is the foundation. A session in the middle sees a larger trusted base than the one
   before it, and that is the decision rather than a defect.

Everything else is proved. The connectives are definitional extensions, the numerals are
definitions, and every arithmetic lemma is derived. If a change makes the axiom count move, it is
either deliberate and needs a record in `docs/adr/`, or it is a defect.

## Conventions here

**Add a lemma by proving it, not by asserting it.** `Kernel.assertAxiom` exists and is named so that
it reads as what it is at the call site. Reach for `Arithmetic`, `Ring`, or a hand derivation
first; the file already contains a dozen worked examples of what a hand derivation looks like.

**A case split about a proposition is `Classical.cases`, not `LT_TOTAL`.** Until 2026-09-10 the
theory of the reals was the only supplier of a disjunction here, so a proof by cases could only be
about an order. `Classical.standard` now has the excluded middle, `cases`, `contradiction` and
`ext`, and a development that wants them takes the extension rather than the bare `Logic.standard`.

**A function defined by cases is written with `COND`, which `Classical` defines.** Until 2026-09-12
there was no conditional constant anywhere in the chain, so a definition by cases had nothing at all
to write its cases with. `COND p a b` is `select (\x. (p ==> x = a) /\ (~p ==> x = b))` and costs no
axiom, which is why the count of nineteen above did not move when it landed; what it costs is a
constant in the signature and a row in `docs/reading-register.md`. It lives in
`modules/logic/.../Classical.scala` rather than in a development, because a constant defined in a
development is unreachable from every link below it. It has **no spelling of its own**: it is
written `COND p a b`, and `if p then a else b` would be a change to the parser and the printer
rather than a row in the precedence table. Its first use outside the file that defines it is
`Rotation`, where it is what lets a caller hand `WORD_MAKE` a function that is already padded.

**A numeral belongs to the type its context forces, and there are two.** Until 2026-09-12 a digit
string was always a `real`, because `Parser` decided from the declared type of `1`; `Power 2 3`
could not be written, since `Power : real -> num -> real` wants a real base and a natural exponent.
`Peano` now declares a second encoding (`NUM_ONE`, `NUM_BIT0`, `NUM_BIT1`, all defined, no axiom)
and the elaborator decides: a numeral takes a metavariable and is expanded once unification has
said what its surroundings required. Three consequences a reader meets immediately:

- **`ZERO` prints as `0`**, because `ZERO` is the encoding's zero rather than a fourth constant
  beside it. `0:num` and `ZERO` are the same term, which is what keeps every lemma about `ZERO`
  reachable from a statement written with `0`. `SUC ZERO` and `NUM_ONE` are still different terms
  with the same value; `NUM_ONE_SUC` is the bridge, and `Successor` is what walks it.
- **A numeral nothing determines is refused** where the theory reads two, and taken where it reads
  one. The escape is `2:num` or `2:real`, which the parser did not read before.
- **A caller that knows the type says so in the call, not in the text**: `Signature.term(text,
  expected)` rather than an annotation inside the string. The measurement is in `Parser.term`'s
  docstring: of seven refusals across a consumer's 630 hand-written texts, all seven were
  unambiguous to the caller, and the text is the thing a reader compares against the informal claim.

**An operator symbol stands for more than one constant, and the elaborator picks which.** The
numerals' rule one level out, landed 2026-09-15 as `docs/adr/0018`. `+`, `*`, `<` and `<=` are
`num`'s as well as the reals', so `!n:num. n + 0 = n` reads and is proved where until that day it
was refused with "real and num cannot be the same type". `Notation` gains no types: it hands back
every candidate for a symbol and the parser, which has the theory, elaborates against the shape the
candidates share and reads the answer back after unification. Overloaded only where the operation
is the **same** one: `-` and `/` are truncated and floor over `num`, so they keep the prefix form
and a reader who writes them is told which constant to reach for.

Four things a reader meets immediately, and the last two are what the change cost rather than what
it bought:

- **Nothing printed moves for the reals, and 135 statements move for `num`.** The criterion is
  the one the measurement used, and it is written down because without it the figure cannot be
  reproduced: of the statements whose text changed between 7.0.2 and 7.0.3, compared by **name**
  rather than by line, 135 carried a `:num` binder beforehand. The 136th changed without one and
  is `le` becoming `real_le`. This sentence read "135 of the library's 436" until 2026-09-16,
  and the denominator was the library's size on the afternoon it was written: a count of what
  moved at one past event does not drift, and the size of the library does, so the ratio was
  true for a day and nothing failed when it stopped being. The card that asked for the work
  predicted 172 of 427 and no criterion on the population reproduces that pair, so a 172 found
  anywhere is the prediction rather than a measurement.
  `NUM_DIVISION_UNIQUE` is the one to look at: it was `NUM_ADD (NUM_MUL x y) z = ...` and is
  `x * y + z = x * u + v /\ z < x /\ v < x ==> y = u /\ z = v`, which is the uniqueness of quotient
  and remainder as anybody would write it. `docs/reading-register.md` gained more than
  `docs/lemmas.md` did, and those are the rows nobody has read.
- **A text whose type nothing determines is refused, and that now includes a text made only of
  digits.** `0 < 1` at the widest signature is ambiguous in two ways at once and is refused naming
  both; `(0:real) < 1` reads. The escape `Signature.term(text, expected)` does **not** reach this
  case when the text is a proposition, because the type a caller can pass is then `bool` and `bool`
  says nothing about the operands. A caller whose ambiguity is inside an equation annotates in the
  text, which is what `Algebraic` does when it builds a polynomial out of variable names.
- **A constant's name is never a symbol any more, and three were.** `Real.Addition` was literally
  `"+"`. It is `real_add`, with `real_mul` and `real_lt` beside it, and `le` became `real_le` so the
  four read alike. `Real.Zero` is still `"0"` and `Real.One` still `"1"`: the same defect, left
  alone on purpose, because they belong to `docs/adr/0012` rather than to this change.
- **`Arithmetic.ringOrder` needed the product to sort before the sum, and got that from ASCII.**
  `*` precedes `+` in ASCII and `real_mul` does not precede `real_add`, so the rename reversed a
  comparison the canonical form depends on, and associativity stopped flattening. **One corpus entry
  in `PolynomialSpec` caught it and **no other test in the repository** did.** The ranking is written down in
  that file now. Read it before touching any order a normal form depends on: the general lesson is
  the one the file already carried about `num`, which is that such an order must not be a property
  of how two constants happen to be spelled.

**A numeral reaches a recurrence only through `Successor`, and until 2026-09-13 it did not reach
one at all.** Every recurrence over `num` is stated at `SUC n`, and `2:num` is `NUM_BIT0 NUM_ONE`,
so nothing written as a numeral hooked anything: `Power x 2 = x * x` was not provable, and
`Bounded.prove` still takes a bound spelled `SUC (SUC ZERO)` and refuses one spelled `2`. The
driver is `chain.successor`; `spell` puts a numeral into the successor form and `expand` opens a
power at a written exponent. It is **aimed** rather than a rule set turned loose, because the five
rules over a whole goal would open every numeral of `num` in it and a modulus of ten thousand
becomes a term with ten thousand nodes, and it derives each expansion over a **variable** base
because otherwise a numeral inside the base is opened too. A caller whose claim is not about a
power does the same thing in two lines with `spell` and `Kernel.eqMp`, which is what `Bounded`
needs and why the spelling is published as an equation rather than as a term.

**The algebra side has known conditionally-valid rewrites**, and they are not defects there: a
simplifier that carried every side condition would be unusable. `ValuePreservationSpec` pins them
by example, with the value each one changes. Do not build anything that trusts them.

**An assertion is only as good as the thought somebody gave to what would make it empty.** Half the
guards here rest on that and none of them used to say it. `RestsOnSpec` asserts that the reach
report's library holds names the searchable one does not, and on 2026-09-12 that is what refused a
change which would have made the assertion **vacuous rather than false**: adding the classical
axioms to `Library.of` would have emptied the difference it checks, and an empty difference passes.
`ProposeSpec`'s buckets are the same discipline from the other side, since a bucket that quietly
stopped receiving anything would read as a clean result. When writing a guard, ask what input makes
it trivially true, and assert against that too.

**A search may add a theorem and must never take a refusal away.** `Prove` asks `Chaining` last, and
its failure leaves whatever refusal the shape rule chose. The rule that class is about is that the
procedure whose fragment recognises the goal's shape is the one whose refusal is reported, and a
search recognises no shape: it either reaches the goal or does not, so it has no claim on the
message. The one place the order is reversed is the propositional address, where `Minimal` runs
before `Propositional` and the **second** refusal survives, because the first names a fragment that
is no longer the only one.

**And the order candidates are tried in is the whole of whether a bounded search works.** Sorting by
fewest obligations is the obvious order and it is wrong here, measured on 2026-09-15: `DOUBLE_NEGATION`
matches every goal at all and owes `~~goal`, `LT_FROM_ZERO` owes `0 < goal - 0`, and each owes one
obligation, so each sorts ahead of the lemma that settles the goal. The lemma that works ranked 4, 5
and 3 by count and 1, 2 and 0 by the total size of what is owed. At forty expansions the miniF2F
corpus cost 2.45 times its own baseline and proved nothing new; at ten under the right order it is
back at baseline and keeps every goal. A candidate whose obligations are smaller than the target is
making progress and one whose obligations are larger is not.

**A tactic that cannot settle a goal must refuse.** `Ring` and `Linarith` are decision procedures
for small fragments and they say so by failing on the rest; `Translate` refuses what the theory has
no constant for, by name. A tactic that guessed would be worse than one that stops.

**Specialise a library lemma by the instance you want, not by position.** The order a lemma's
quantifiers are written in is not part of any contract: it follows from how the lemma was derived,
and on 2026-09-13 a derivation rewritten for an unrelated reason reversed the binders of `SUM_SUC`,
`POWER_SUC` and `PROD_SUC`. A consumer specialising those positionally stopped building, and it
stopped only because the two arguments had different types. Where two leading quantifiers share a
type the reversal is invisible and what comes out is a theorem that is true and is not the one the
caller meant: of the library's 495 lemmas, 322 have two or more leading quantifiers and **295 of
those have two that share a type**. `Rules.specTo` takes the body to be obtained and finds the
instantiation by matching, so the order is nowhere in the call; `Rules.specToReduced` is the same
where the caller's argument is a lambda and the instance carries a redex, which is a **different
theorem** and therefore a different operation. Neither protects the positional call sites that
remain.

That count is of binders sharing a type anywhere in the prefix, and the obvious next thought, that
only adjacent ones are realistically swapped and so the real number is smaller, is wrong and was
measured on 2026-09-13: of the sites a whole suite run reaches, 204 specialise a lemma with two
alike binders and 202 of those have two alike and adjacent (measured before `Magnitude` joined the
chain, which added nine alike-binder lemmas and no call sites, and before `Concatenation` joined it
on 2026-09-16, which added both: that file specialises `WORD_EXTENSIONALITY` by position at two
arguments of one type. The pair of numbers is a reading with a date rather than a property, and what
it was for is the ratio between them, which nothing since has moved). A lemma with three binders of one type
has adjacency anyway. The narrow reading and the broad one are the same number.

**The order the rewriting sorts by is not the kernel's.** `Arithmetic.ringOrder` compares by the
term under any negations first, so that a term ends up next to its own negation and the two cancel.
Changing it to the obvious structural order breaks cancellation silently.

**A model answers at a point, and `None` is not `false`.** `Evaluate` returns nothing where the
model has nothing to say: a constant nobody interpreted, `inv 0`, a quantifier over the reals.
Every caller skips such a point rather than counting it. `Refutation` keeps seven answers apart for
the same reason: a point found by sampling, a point found by solving, no witness at the points that
answered, no point that answered at all, a decision that the premises cannot all hold, a decision
that the claim cannot be refuted, and a refusal because sampling cannot settle a question of that
shape. Collapsing any two of them turns "I could
not ask" into "I asked and it was fine", which is the one way this machinery can mislead.
`docs/adr/0005` has the rest, including what changed on 2026-09-05 and what it did not change.

**A probe goes in `scratch/`, never under `modules/`.** That directory is ignored by git and is in
no sbt source set, and it exists because the alternative happened: a session left a throwaway spec
under `modules/` and the next run of `sbt test` on this shared checkout failed for somebody else
with an error about a file they had never seen. If you are delegating to an agent, repeat this in
the briefing: a rule in this file does not reach an agent the project did not write.

**Property tests carry their sample count and the measurement that chose it.** They exist to probe
the design, not only to guard against regressions, so a new invariant belongs in one of them rather
than in another example.

## Where this is going

The goal is exploration: proposing identities quickly and having each one certified, so that a long
symbolic development does not rest on a step that was only conditionally true. `modules/tactics`
is where that loop lives.

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
condition at all wants the integers, which `docs/adr/0007` puts later.

**`defineType` has three uses now and they were all built the same way.** `num`, then `prod` in
`Product.scala`, carved out of `'a -> 'b -> bool` the way `pair.ml` does it, then `word` in
`Word.scala`, a length and a padded function held together in a pair. The second and third exist
because lists, matrices and index types were all one missing primitive, and it was the pair.

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
fifteen derived facts including associativity, both units, and an induction that extends a word **on
the right** rather than on its length. Before it, `?x y. w = x u y` was not a sentence this
repository could write, so of a factor nothing could be said, not even wrongly.

It is **not** a development of its own for `Rotation`'s reason, and the difference is the thing to
carry: `NUM_MOD` really is outside `Word.standard`'s signature, and `NUM_ADD`, `NUM_SUB`, `NUM_LT`
and `COND` are all inside it, so this could have gone in `Word.scala` and would have built. What
decided it is size and subject, and `ConcatenationSpec` asserts the four constants are there rather
than leaving the claim in prose.

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

Number theory on `num` is `Modular`, a link in the chain since 2026-09-12: divisibility with the
antisymmetry that is false over a field, congruences with their compatibility with addition and
multiplication, division with remainder in both halves, `NUM_DIV` and `NUM_MOD` as functions that
denote and are total, the greatest common divisor, Bezout, and Euclid's lemma with a definition of
prime. `Bounded` discharges `!i. i < k ==> P i` at a concrete bound by proving the instances and
assembling them, and was the one development that sat beside the chain's extension order rather than
in it, because it declares nothing. It is one of three now: `Primes` and `Deduction` joined it on
2026-09-14.

**`Primes` holds theorems about the primes that are results rather than infrastructure**, and today
that is two. Euclid's, `!n. ?p. NUM_PRIME p /\ NUM_LT n p`, which is what "there are infinitely many
primes" says in a logic with no notion of an infinite set. And `NUM_SQUARE_NOT_DOUBLE`, that no
square is twice a square at a positive denominator, which is the arithmetic content of the
irrationality of the square root of two and is **not** that sentence: there is no square root on the
reals here, so the classical statement cannot be written and the name does not pretend otherwise.
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
pair. That is what lets `Descent` define a predicate by recursion on a code, and it is what will let
the object theory quantify over sub-codes boundedly, which is what Delta-0 means. The bound is not
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
those lines were an instance of, and the family is what the next step needs rather than the
instance: Goedel's argument substitutes the numeral **of** a number, and there is one of those per
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
of axioms. It is what the object-level derivation will have to formalise and what every meta-level
argument about the embedded theory chains with. Read as D2 it makes the remaining work look done.

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
the reason the note four hundred lines above gives. `DeductionSpec` asserts the theory it hands on
is the one it was given, constant for constant, so a definition arriving here goes red rather than
passing unnoticed.

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

The quantifier is the only interesting clause, and the bookkeeping is the whole of it: descending
past `!b. ...` carries `~(b = i)` down, and `NUM_FREE_TERM i (NUM_CODE 0 b)` is `b = i`, so the
inequality carried down is exactly what refuses the variable at the bottom. Shadowing works because
the list is prepended to, and `LanguageSpec` asserts that rather than leaving it to a reading: none
of the codes this repository builds binds one index twice. And above
that, the thing Goedel's argument actually needs, which is `Prov` as a formula **of the object
language** with one free variable rather than as the predicate `NUM_PROV` of the ambient logic.
**D1, D2 and D3 are statements about that formula, so not one of the three can be stated yet.**

What is above that is not written: that object-level `Prov`, the diagonal lemma, and then D1, D2
and D3. `docs/adr/0013` says why the last of those is its own piece of work rather than a helper
inside this one, and it is the part most likely to be underestimated.

**Discharging the freeness condition at a concrete code was a fourth entry on that list until
2026-09-15**, fifteen lines below the paragraph that says `Language.notFreeIn` does it and
`DeductionSpec` spends it on an actual axiom of PA. The change that built it left the list alone.
A list of what is missing is the one kind of list that goes stale silently: every other figure
here is pinned by a test that fails when it moves, and nothing fails when an item on this one
gets built.

**The set defined by rules is `Inductive`, and it is `Chain.widest` since 2026-09-16.** One
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

What is still not proved is that a **series** converges, which is the comparison test and nobody has
assembled it. So `exp 1 > 2` and `sin x * sin x + cos x * cos x = 1` are **statable and unproved**,
which is a different answer from the parse error they used to get and is the whole reason to define
the constants before the analysis rather than after it.

Three things in those derivations were harder than they look and each is recorded where it happens.
Halving a tolerance is `Linarith`'s, because a numeral denominator is a rational coefficient to it
and `0 < e ==> 0 < e / 2` is inside the fragment it decides. Putting two indices together is
`Peano.NUM_LE_ADD` and not a maximum, because `num` has none. And the rewriter is given **two**
equation sets rather than one: `NUM_ONE_SUC` rewrites the `1` inside a bit encoding, so with it in
the set the `2` in the cosine's exponent becomes `NUM_BIT0 (SUC ZERO)` and stops matching a lemma
proved about `Power 0 2`, which is the refusal that produced the split.

What is not there yet, in the order the work seems to want it: a greatest common divisor anybody can
**compute**, since `NUM_GCD` and `NUM_DIV` are both chosen rather than calculated and Euclid's
algorithm is a definition by well-founded recursion, which this system does not have; then the
integers and the rationals, and then the reals as a construction rather than an assumption. `docs/adr/0007` is the order and `docs/adr/0006` is the rule that
unlocked it. `docs/adr/0004` records why the reals were axiomatised rather than constructed, and the
same reasoning does not extend to the naturals.

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

**A domain claim was a hand derivation and is no longer necessarily one**, and until 2026-09-15
this paragraph said it was, in the same words as the header of the file that had already stopped
being an example of them. `Ring` and `Linarith` decide fragments of the reals and have nothing to
say about an arbitrary axiom, which is the true half and is what the sentence was built on. What
reaches a domain is the propositional skeleton: `DomainTheorySpec` settles the same claim a second
time through `Propositional` and keeps both routes on purpose, because the comparison is the
finding. Same theorem, same one domain axiom, and **one foundational axiom where the hand
derivation spends none**, since `Propositional` decides classical validity and closes with double
negation while the hand derivation is intuitionistic throughout. `Minimal` is the procedure that
would cost nothing and it refuses anything with a negation in it, which a domain criterion is made
of, so neither procedure here covers such an argument at its real cost.

The caller still spends the axiom: the instance is specialised and detached by hand, and what the
procedure gets is a tautology over the domain's constants as atoms, with no meaning given for any
of them. So the promise is still accounting rather than search, and a route that reaches the
theorem while moving the accounting has bought fewer lines at a price named in the currency this
repository exists to report.

Such a theory sits beside the chain and must stay there: two theories that axiomatise one name are
the case `docs/adr/0008` leaves open, and `SoundnessAttackSpec` still derives `|- F` from it.

## Working agreements

**Verify before recording as done.** A tactic is built when it has proved something end to end, not
when it compiles and its unit tests pass.

**Stale references are worse than missing ones.** When something moves, the references move in the
same change: a document naming a file that is gone gets consulted and believed.

**Ask before anything irreversible or outward-facing.** Approval for one action is not approval for
the next.
