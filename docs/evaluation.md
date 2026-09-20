# Evaluation

**EXCERPT — for anyone scanning the index:**
Where the system stands against the current benchmarks for provers, which is nowhere on three of the
four shapes it lists and for three different reasons, and measured on the fourth; the measurements
that can be taken today and what they show; where a language model can be put into the loop with the
kernel still checking everything, and where it cannot; and the order to build in. It is the document
to read before pointing a model at anything, and before promising a result. It does not explain how
to prove things, which is [proving.md](proving.md), and it does not argue the design, which is
[architecture.md](architecture.md).

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

The survey behind this was run on 2026-09-03. The timings were taken on 2026-09-04 on an Apple
Silicon laptop, single runs after one warm-up call, and anything under about 50 ms is noise.

## Against the benchmarks

Two of the four shapes below are zeros, and the interesting fact is that they are zeros for the
same reason, which is not about proving power. Of the other two, one stopped being a zero on
2026-09-10 and one on 2026-09-11, and both now carry a measurement rather than an argument.

| Benchmark | What a problem needs | Why the score is zero |
|---|---|---|
| miniF2F, PutnamBench, ProofNet | naturals, induction, sums, sequences, trigonometric and exponential functions | **Not statable as a corpus, and measured on the slice that is.** Of miniF2F's 244 test statements, read from the vendored file rather than transcribed, this system can state **39**. The other 205 are blocked, and track M names each blocker with a count: 104 carry a hypothesis whose syntax the reader does not take, 18 quantify over a type the tactics have no signature for, and the rest name a function the theory has no constant for. What used to stand here, *"a run would still produce parse errors, not failed proofs"*, was written before the naturals and before arithmetic on them, and the measurement refutes it: the run produces both. **The proof count is in track M and is not a benchmark figure**, for the reason that section gives |
| CASC, SMT-COMP (LRA, NRA) | proof search over first-order or arithmetic problems | **No search at these shapes, and the searches there are do not reach them.** `Propositional` decides the classical propositional fragment and certifies it, `Chaining` chains lemmas backwards over the library, and `Intuitionistic` backtracks over the whole intuitionistic propositional fragment, negation included, at no axiom — Dyckhoff's contraction-free calculus, `docs/adr/0022`. `Minimal` was the third of these until 2026-09-18 and is now the **address** rather than a search: it is the gate whose `reads` and `declines` decide that a goal is propositional at all, and the search it used to publish is the calculus itself, which `docs/adr/0023` decides and `PropositionalRouteSpec` measures: of the 1114 formulas of at most six nodes on two atoms that take this address, 58 move from one axiom to none and 98 stay classical-only. There **is** a clause queue since 2026-09-15, inside the solver in `modules/sat`; what there is still no trace of is a **given-clause loop**, which is the architecture these two competitions are about: no saturation, no forward inference over a clause set, no active and passive sets. **Since 2026-09-18 that absence is decided rather than open**, and `docs/adr/0029` is the record: not one of the miniF2F statements this system reads and does not settle is a first-order search problem — every one is `!vars. H ==> C` with no alternation, the hypotheses are already facts since `docs/adr/0025`, and what is left to decide is arithmetic in each of them. That record enumerated eighteen of them on 2026-09-18 and the count is not repeated here, because it falls whenever the prover gets stronger: two of that eighteen were one instance of `SQUARE_NONNEG` that `Linarith`'s degree bound refused, and the completed square of `docs/adr/0032` settled both the same day, and `ReachSpec` prints the ones left by name on every run. The classification is what the decision rests on and it does not move with the count. Not one of them reaches a first-order or an arithmetic problem, so the zero is unchanged and the reason is still the fragment. This cell denied a choice point until 2026-09-15 and denied a clause queue until later the same day. The first was corrected by measuring what `Minimal` already did and the second by building a solver, which is the difference between a sentence that was wrong and a sentence that went out of date. `DocumentationSpec` holds the first against the code so it cannot come back, and holds this cell's list of them against what `Prove` reaches, which is why there is no longer a count of them here: this cell carried one, the front page carried another, and a count written in two documents is the defect `Generated`'s docstring collects five instances of |
| TPTP, the RNG and FLD domains | equational reasoning about rings and fields | **No search**, and this is the diagnostic zero: the mathematics is in range, the goals can be written down, and nothing here goes looking for an EQUATIONAL proof. `Ring` and `Field` decide or refuse, and `Minimal`, which is the one thing here that searches, is propositional and cannot read a goal of this shape. Roughly four hundred problems |
| Kernel re-checking (the Lean Kernel Arena shape) | a proof object a second checker can replay | **Measured since 2026-09-10.** A theorem records its derivation and `modules/checker` reads one without touching a kernel rule, over a serialised proof or in this process, so this row is differential where it used to be adversarial. See the section below |

The owner's own targets are in the first row. A Collatz statement needs an integer index, a
binomial coefficient and a cosine, none of which the theory can write; P versus NP needs machines
and asymptotics; the Riemann hypothesis needs the complex numbers and analytic continuation. These
are not hard for the tactics. They cannot be written down. The type-definition rule that had to come
first landed on 2026-09-10 and the naturals with it. `docs/adr/0007` is the order for what comes
after, the integers and the rationals as quotients and then the reals as a completion, and
[proving.md](proving.md) keeps the list of what is missing beside what has landed. Neither order
reaches all three targets above: machines, asymptotics and the complex numbers are past the end of
both.

## What can be measured today

Each track below is runnable against the code as it is. K, R, L, F, O, D, T and C exist as suites and
P is covered by property tests, two of which were written for another purpose. Nothing on the list is
now unmeasured.

- **What a theorem rests on, which is not a track and is what the record bought first.** A proof
  names the axioms it reaches, so `12 * 12 = 144` is 1132 inferences over five of the sixteen and
  touches neither the order nor completeness, and `0 < 1` touches the order and not the ring. A
  sequent has always said what was assumed; this is the first time anything said what was
  *believed*. `ProofRecordSpec` asserts it per theorem, and the cost was measured beside it:
  twenty proofs of a squared binomial retained 2.4 MB for 64800 inferences, about thirty-seven bytes
  a step, and walking a four-thousand-step proof takes under two milliseconds. **The inference
  figure is from before the two repairs of 2026-09-11 and has not been re-measured since**, so the
  megabytes and the step count are both stale in the same direction and the ratio between them,
  which is what that sentence is about, is not: the bytes a step are a property of the record rather
  than of the rewriting. The same question
  asked of a whole corpus rather than one theorem is in the section below: fifteen of the sixteen
  axioms take part in another library's ring test file, and completeness does not.

- **K, kernel adversarial corpus.** Must-reject and must-accept cases drawn from the historical
  soundness-bug record: capture through `inst` with an open term, a type-variable collision in
  `instType`, abstraction over a variable free in a hypothesis, a definition with a free variable
  or an escaping type variable, `eqMp` on sides that print alike, forgery by reflection. The
  capture items were live failures on 2026-09-03 and are fixed and pinned. Exists, since
  2026-09-10: `SoundnessAttackSpec` in `modules/theories` holds the corpus as one artifact, and the
  counts are in the section below.
- **M, reach into somebody else's corpus.** miniF2F's 244 test statements, read from the vendored
  file rather than transcribed, put to the whole tactic surface through `Cost`, with the buckets kept
  apart: what could not be read, what could not be said, what was attempted. Exists since
  2026-09-11: `ReachSpec` in `modules/tactics`, and the section below. It found two defects in one
  run, which is the argument for reading somebody else's corpus rather than writing one's own.
- **P, Pollack consistency.** `parse(show(t)) == t` over generated terms. `RulesPropertySpec`
  runs it over formulas, `NumeralSpec` over numerals, and, since 2026-09-07,
  `NotationRoundTripSpec` over the arithmetic notation, which is the one every axiom string is
  read through and the one a session is shown its formalisation in. Two hundred statements a run,
  shrinking off because a precedence disagreement is a property of a term's context and shrinking
  removes the context. It found a defect on its first run: a free variable prints as a bare name,
  a bare name carries no type, and equality is polymorphic, so `x = y` between two reals was text
  the reader refused. A bound variable never had the problem, because its binder prints an
  annotation. `Show.annotated` now exists for the case and `Readback` reaches for it only when the
  plain form does not come back, deciding by trying rather than by predicting.

  **The generator was not the population, and on 2026-09-12 that cost fourteen statements.** Every
  statement it produces is over `real`, because that is the notation whose precedences can disagree;
  nothing it produces has a type variable in it. `Product` and `Word` landed fourteen lemmas that
  do, the printer wrote `prod(a, b)` where the parser reads `prod('a, 'b)`, and this property passed
  throughout while `docs/lemmas.md` carried fourteen lines nobody could read back. The same file now
  also asserts over the document itself — all 186 statements, through `Chain.widest`, failing by
  naming the lemmas — which is a population that grows when the repository does rather than one a
  generator was written for.
- **R, RING coverage and scaling.** Mathlib's own test file for its `ring` tactic, read rather
  than transcribed, plus the ladder below. Exists: `RingCorpusSpec` in `modules/tactics`, over
  `third-party/mathlib/MathlibTest/Tactic/Ring/Ring.lean`, frozen at the commit its notice names.
  The counts are in the section below, and the suite asserts them against it.
- **L, LINARITH coverage.** Mathlib's own test file for its `linarith` tactic, read rather than
  transcribed, the same arrangement as track R one file over. Exists: `LinarithCorpusSpec` in
  `modules/tactics`, over `third-party/mathlib/MathlibTest/Tactic/Linarith/Basic.lean`, frozen at
  the commit its notice names. The counts are in the section below and the suite asserts them
  against it. The ladder of n hypotheses is measured in the section on the certificate search.
- **F, the field fragment against the same corpus.** Two questions of the file track R reads, not
  one. What `Field` *costs* on the goals track R measures, which is whether it charges a hypothesis
  where none was needed; and what it *adds* among the goals track R's selection rule throws away,
  which are the declarations upstream closed with `field_simp` and then `ring`. Exists:
  `FieldCorpusSpec` in `modules/tactics`. The counts are in the section below and the suite asserts
  them.
- **O, oracle certification rate.** Expressions produced by a generator, each paired with its own
  expansion or simplification by the algebra system, put through `Oracle.certifyExpansion` and
  `certifySimplification` and bucketed certified, outside the fragment, and inside the fragment
  but unproved. The third bucket must be empty; any member is a defect in the algebra system or
  in RING, and a finding either way. The corpus is generated rather than transcribed so that
  nobody can adjust a pair to pass, and because the alternative cannot be built: the algebra
  system's own tests state their expected sides as printed strings, and `core` has no parser to
  read one back. Exists: `OracleCertificationSpec` in `modules/tactics`, 40 expressions at depth
  2 with coefficients within ±3, all certified, the third bucket empty; 180 expressions at deeper
  settings were run while it was written, with the same result.
- **D, discovery precision.** Labelled candidates, a third true and in the fragment, a third
  near-misses by one coefficient or sign, a third true and outside the fragment; report screen
  recall and precision, certification rate on survivors, and the size of the unsettled bucket.
  Exists, since 2026-09-10: `DiscoveryPrecisionSpec` in `modules/tactics`. The counts are in the
  section below.
- **C, the Collatz differential.** Every closed form in `CollatzSeries` against exact integer
  iteration, as a build-failing test. Exists: `CollatzSeriesSpec`. See the finding at the end.
- **T, translation traps.** One sentence in the author's words and two readings of it: the one that
  says what it says, and one a careful person might write instead. The measurement is not whether
  the obvious reading is found, it is whether a wrong one can be told apart. Exists:
  `TranslationTrapSpec`. The counts are in the section below.

Nothing on this list is a public leaderboard, because there is no public leaderboard this system
can enter yet. That is the position, stated as it is.

### Track R', the second reading, measured

`modules/checker` walks a theorem's derivation and checks every step against a rule it implements
itself. It depends on the kernel for the data a theorem carries and reaches for none of its rules,
which a scan of its sources asserts: the typing, the closedness, the substitution, the closing of a
binder and the beta step are written again there, over a term representation of its own.

What the checker's own machinery is checked against is the kernel's, and it is not shared with it:
each of the typings, substitutions and beta steps below is read once, through the extractors.

The tables below are **generated** by `sbt "tactics/Test/runMain garden.xeno.symbolum.tactics.Evaluation"`
and pinned by `FiguresSpec`. The counts are the second reader's own, over the proofs
`garden.xeno.symbolum.checker.Replayed` holds, which is the same list `ReplaySpec` and `SerialisedSpec`
replay: a count of replayed theorems is a claim about a list, and a list nobody can point at is not
a measurement.

**None of them is refused**, and there is no row saying so: the generator stops rather than
typesetting a refusal of this system's own proof, so a table exists at all only when every proof in
it held. The second row counts the wrong claims put to the rule check directly, which is the half
nothing else can reach — there is no way to obtain a wrongly derived theorem from the kernel in
order to show the checker one.

<!-- generated: replay, do not edit below this line -->

|  |  |
|---|---|
| theorems replayed here | 12 |
| wrong claims put to the rule check, in `CheckSpec` | 11 |

| Theorem | Inferences | Axioms reached |
|---|---|---|
| `0 < 1` | 1757 | 11 |
| `0 < 12` | 2167 | 12 |
| `12 * 12 = 144` | 1132 | 5 |
| `(x + 1)^2` expanded | 2251 | 8 |
| `x < y /\ y < z ==> x < z` | 4122 | 9 |
| `(x * y) / y = x` | 1757 | 8 |
| `p /\ q ==> p`, propositional | 199 | **0** |
| `((p ==> q) ==> p) ==> p`, found by a solver | 1256 | 1 |
| an on-call rule's own claim | 295 | 1 |
| `ADD_SYM`, an axiom of the reals | 1 | 1 |
| the successor's properties | 403 | 2 |
| induction over the naturals | 625 | **0** |

<!-- end generated: replay -->

Every count in that column came down twice on 2026-09-11, and the two are worth keeping apart
because they say different things. The rewriter stopped building a theorem to report that it had
done nothing, and with it went the congruence and the transitivity that existed only to carry
those: that repair touched the rows that rewrite and left induction over the naturals at 790, which
is a hand derivation. Then `Conv.refl` began holding the reflexivity of an atom instead of building
one per use, and **that** one reached every row, induction included, which fell from 790 to 625. A
hand derivation builds the same leaves as any other proof; what it does not build is the idle steps.

**That last figure said 199 until 2026-09-12, and it was never true.** Nothing in the kernel, in
`modules/logic` or in `Natural.scala` has changed since the day it was written, so the derivation
being counted is the same one; it measures 625 and it measured 625 then. 199 is what the
propositional theorem two rows above costs, and it was copied out of the wrong line of a test's
output — which is also why the drop it implied, three quarters of the proof, never matched the 23%
the repair removed everywhere else. The row is generated now, and that is the repair: the number in
it is the one the checker returns for the proof the row names.

The "checked in" column is gone rather than re-measured. It was milliseconds on this machine, and
this machine has read the same suite at 41 seconds and at 6 minutes 39 on the same day.

**What it catches and what it does not.** A theorem that was not derived at all; a step that is not
an instance of the rule it claims; and a rule the kernel implements differently from the way the
checker does, which is the case a second implementation exists for. Everything past the shape is
re-decided, which is where the 2026-09-03 hole lived.

**There are two routes in and the second one is text.** The table above is the in-process route,
which reads the kernel's terms through the kernel's extractors: a defect in **those** would tell it
the same story they tell everyone. `Kernel.Proof` writes a derivation out as characters and `Parse`
in the checker reads one back, naming no kernel type at all, which a scan of that one file asserts.
Both routes end at the same rule check, so there is one reading of each rule rather than two.

The axioms found over text are the same set as the axioms found in this process, for every theorem
in the suite, and `SerialisedSpec` asserts that rather than reporting it. What is still shared is
the writer, and nothing else.

<!-- generated: serialisation, do not edit below this line -->

| Measured on `12 * 12 = 144` | As text |
|---|---|
| steps, and the distinct terms they are written over | 1132 steps, 2048 terms |
| the nodes a writer without sharing would have emitted | 40860 nodes, a sharing factor of 20.0 |
| its size | 66690 characters, 58.9 a step |

<!-- end generated: serialisation -->

**A term is written once however many steps use it**, which is the property that decides whether
this is usable: those 2048 records stand in for **40860** term nodes the steps would otherwise have
written out, a factor of twenty, and a format that copied a term into every step would be quadratic
in the thing that is already the largest number here. References go backwards only, so the
reader is one pass with no fixup.

The comparison used to be made against the step count, and it stopped working on 2026-09-11 without
anything about the format changing: the rewriter halted a third of the proof's nodes, the vocabulary
of terms did not shrink with it, and a proxy that had held only because redundant steps reuse terms
came out the wrong way round. `SerialisedSpec` measures the property itself now.

**What is left shared is the writer, and nothing can remove it.** Something has to put the proof
down. What a checker can do about a writer is refuse what it wrote, and that is measured rather than
argued: a conclusion swapped for another term in a written-out proof is caught by the rule check,
because what the step claims stops being an instance of the rule it names.

**The refusals are exercised, and that half is the one nothing else can reach.** There is no way to
obtain a wrongly derived theorem from the kernel in order to show the checker one, so the rule check
takes data rather than a theorem and nine wrong claims are put to it directly. A checker tested only
on proofs that are right has been tested on nothing.

**An axiom is reported and never verified.** Nothing can verify one: that is what a trusted base is.
A proof of `ADD_SYM` is one step and one axiom, and the checker says so rather than passing it.

**The last row of the table is the finding.** Induction over the naturals reaches **no axiom**,
while the successor being injective and missing zero reaches both. Induction follows from the
definition of `NUM_REP` alone: infinity is what makes the naturals infinite, not what makes
induction hold, and if `ind` had one element then `num` would be a singleton and induction would
hold of it vacuously. No sequent could have said that, and nobody had noticed it here until a proof
was asked what it rested on.

### Track M, measured

miniF2F's 244 test statements, from `third-party/minif2f/lean/src/test.lean`, frozen at the commit
its notice names and byte-identical to upstream. Read, not transcribed, for the reason tracks R and
L give, and every count below is produced by `ReachSpec`.

**This is not a benchmark row and the figure below is not a pass rate.** miniF2F is from 2021, it is
saturated at the top, it contains statements the community has repeatedly had to correct, and the
field has moved to PutnamBench and FormalMATH. What is worth publishing about it here is the
**width of the reader** and the **histogram of what blocks the rest**, which measure the reach of
this theory and are not comparable with anybody else's rate. The proof count is reported because
leaving it out would be its own kind of dishonesty, not because it means anything against Lean.

| | |
|---|---|
| statements in the file | 244 |
| stated, and put to the whole tactic surface | 39 |
| of those, proved | 21 |
| of those, attempted and not settled | 18 |
| never attempted | 205 |
| wall clock, whole corpus | 32 seconds |

**The date these figures carry, which they did not carry at all until 2026-09-17.** Every count in
the table above and in the histogram below is the run of `ReachSpec` at `fff7434`, read off the
whole-suite job of that push's CI run on 2026-09-17 rather than off a laptop. The rule at the end of
this document says a photograph of a live measurement carries its date, and this section was the one
place claiming that arrangement while naming no date, so a reader could not tell whether the
histogram was a week old. The wall clock is the exception and is not from that run: it is an undated
laptop figure, and the same pass took **1 minute 32 seconds** on the runner, which is a different
machine rather than a regression.

The 205 that were never attempted are the roadmap's denominator, and this is what stops them:

| What is missing | Statements |
|---|---|
| a hypothesis whose syntax this reader does not take: `∀` inside a hypothesis, `≠`, `¬`, a function type | 104 |
| `%`, modular arithmetic | 15 |
| a qualified name, `Nat.gcd` and its kind | 13 |
| `ℤ` in a binder | 10 |
| `∑` over a `Finset` | 8 |
| `ℚ` in a binder | 5 |
| `nnreal` in a binder | 5 |
| `ℂ` in a binder | 4 |
| `∏` over a `Finset` | 4 |
| `ℝ` and `ℕ` in one statement, which is a coercion | 4 |
| `∃` inside a hypothesis | 3 |
| a conjunctive goal, which is not split for the reason `ReachSpec` gives | 3 |
| the rest, each a name the theory has no constant for: `abs`, `sqrt`, `!` | 27 |

**The `ℕ` row is gone, and the top row absorbed most of it.** On 2026-09-11 `Translate` gained a
target type: a statement whose binders are all naturals is read through `real_of_num`, so it is a
statement about the image of the naturals in the reals and the procedures that decide the reals see
it. Seventy-four statements left the type bucket; four of them are now attempted, and the other
seventy moved to whatever was blocking them *underneath* the type, which is nearly always a
hypothesis this reader does not parse. That is the histogram doing the job it exists for: the type
was the first obstacle and not the only one, and the table now says which.

Two rows are new because the type test changed direction at the same time. It used to name the
types to reject and read everything else as a real, so `nnreal` and `ℕ+` were put to the prover as
claims about arbitrary reals; it now names the types it understands and refuses the rest. None of
those was ever proved, which was luck: the non-negativity a source states by writing `nnreal` is a
hypothesis, and dropping it makes a different claim.

What is left behind a **type** is the three rows `ℤ`, `ℚ` and `ℂ` of the histogram above, which is
**nineteen** statements, and those wait on `docs/adr/0007` rather than on a translation. This
sentence said eighteen until 2026-09-17 and disagreed with its own table two paragraphs above it,
where the three rows read 10, 5 and 4: each statement never attempted contributes exactly one tally
to exactly one row, which is what makes the rows addable and what `ReachSpec`'s own assertion that
they sum to the three not-attempted buckets rests on. Eighteen is the count in the row above the histogram, of statements attempted and not
settled, and a sum that lands on a figure already in the document is the one shape of arithmetic
slip nothing here would query.

**Two defects came out of the first run, and they are the reason for reading somebody else's corpus
rather than writing one's own.**

The first is the one that mattered. Three statements came back **decided false**, among them
`!x. x * (2 - x) <= 1`, which is true. `Quantified` read `x * x` as an opaque atom, eliminated the
quantified `x`, and the atom went with it, so the guard that refuses an atom the procedure cannot
range over — which sat at the *end* of the elimination — saw a clean answer. A wrong "this does not
hold" is the worst output this system can produce. It is not an unsound theorem, since nothing is
certified and `docs/adr/0005` says a verdict is not a proof; it is worse in use, because a reader
deletes a true conjecture on the strength of it. The check now happens where the fact is read.

The second is cost. `amc12b_2002_p19` took **439 seconds** and then refused, where the next slowest
of the 244 took 25. Three quadratic hypotheses and three positivity facts give a pool of nine,
forty-five pairs, a cubic round on top, and `byRefutation` runs all of it three times. `Linarith`
now has two bounds, `Facts` and `Cubes`.

**What those bounds cut was not measured when they were set**, and the card that said so was right
to. The measurement was taken on 2026-09-11 and it moved one of the two halves of the argument.

They cut provable goals, and `LinarithLimitsSpec` generates the family that shows it rather than
choosing examples: `0 < x1 /\ ... /\ 0 < xn ==> 0 < x1 * x2` is settled by the pairs at every size
and is refused from nine hypotheses up, and the same family with a product of three in the
conclusion is refused at six by the other bound. Both are theorems with the line elsewhere. Of the
244 statements, five reach a bound: four reach `Facts` at fifty-one facts and `imo_1964_p2` reaches
`Cubes` at twenty-seven.

What they buy is **not** what the code said. The note on `Facts` claimed the pair round on fifty-one
facts "takes minutes on a goal it then refuses", and one call of the procedure at 400 takes 15 to
100 milliseconds on every goal measured. The minutes are one level up: `Abduce` runs the procedure
once per candidate premise, so twenty milliseconds here is a hundred times that there. Through the
whole surface, over the six heaviest statements of the corpus: **20.0 seconds at the bounds against
40.6 seconds at 400**, buying one proof. Twice the time on the heavy tail for one theorem, and the
bounds stay where they are.

**And the refusal now says which of the two things happened.** A goal over a bound came back as "no
non-negative combination of the hypotheses gives this", which was false about it: the combination
exists and the search stopped before building it. `BoundReached` is its own refusal for the reason
`NotNormalised` is — a limit reached and a claim that does not follow imply opposite next moves —
and `Remedy` maps it to the limit by name.

**It was two things and it is three.** Separating the bound left "the goal does not follow" sharing
a constructor with "I cannot read the goal", which is the same merge one step along: both were a
`NotOfForm` with a different sentence inside, so a caller could tell a refuted negative check from an
unreadable one only by parsing English. A consumer's harness did not, and reported an exhausted
search as a refutation in a committed artifact. Since 2026-09-12 the answer is `DoesNotFollow` and
every refusal carries a `LogicError.Standing` of `Decided`, `Exhausted` or `Unread`; the same pass
found a third site, in the cubic round, where a bound reached inside the escalation was swallowed
into the refusal from before it, which is the original defect surviving where nobody had written the
exception by hand.

**A third came out of the second run**, and it is the one that says most about this system. When
the naturals became readable, `mathd_numbertheory_234` took 126 seconds and then reported the
missing premise `real_of_num x < 0` for a claim that already assumes `1 <= real_of_num x`: a
premise that makes the hypotheses impossible, which is the one failure `Abduce`'s class comment
says it checks for. The check was being made and its answer misread. `Refutation.satisfying` has
five answers and only two of them decide anything, and the code matched "contradictory" against a
default case, so the three that mean *the question was not settled* were read as *the premises hold
up*. Over the eighteen statements this system attempts and does not prove, that was **275 of the
422 candidates**: sixty-five per cent of every missing premise it has ever reported was never
checked for the failure it claims to exclude. Five of the six worst-affected statements are about
the reals and predate the naturals entirely.

The repair is one bucket rather than a bound: a candidate whose effect on the premises was not
decided is reported as `unchecked` and never as something to assume. It also removes the cost,
because the filter that keeps only the weakest candidates compares them pairwise with a decision
procedure, and its own docstring says it must not be run over candidates that may make the premises
impossible. Those were exactly the ones reaching it. The corpus went from 4 minutes 9 seconds to 32
seconds, and the whole suite from 2 minutes 1 second to 41.

### A cost measured in counts rather than in seconds

The card that asks for the constant factor says that none of its gains can be shown without a cost
corpus, and gives the reason in the same breath: the documents here record the same scale differing
by a factor of two in one afternoon. That is not a flaw in the readings. A wall clock measures the
afternoon it was read in, and this suite ran in 41 seconds and in 6 minutes 39 on one tree on one
day, because something else on the machine was busy.

So the cost corpus is a **census of a proof's nodes**, which is a function of the proof: two runs
agree, two machines agree, and a change that claims to have removed work has to show the count
moving. `Derivation.census` is the mechanism, `Cost.Report.census` carries it, and `CostCorpusSpec`
reports it over the vendored ring corpus rather than over an example.

The table below is **generated** by `sbt "tactics/Test/runMain garden.xeno.symbolum.tactics.Evaluation"` and
pinned by `FiguresSpec`, and the total is printed under it rather than left to the reader: this
census summed to 196623 beside a total line reading 153953 until 2026-09-12, two hand copies each
stale from a different day, and neither of them was caught by anything.

<!-- generated: census, do not edit below this line -->

| rule | inferences over the 37 proofs |
|---|---|
| congruence | 35113 |
| equality elimination | 24387 |
| reflexivity | 15385 |
| transitivity | 14912 |
| instantiation | 12513 |
| beta step | 9272 |
| type instantiation | 5322 |
| antisymmetry | 3572 |
| abstraction | 1388 |
| assumption | 560 |
| axiom | 272 |
| definition | 166 |

They add up to 122862 inferences, of which 15385 are reflexivity, 12.5% of the corpus.

<!-- end generated: census -->

**A third of every proof used to be reflexivity**, and the table below is where that figure lives
with its date on it. Those were theorems built to report that nothing had happened, and the
constant-factor card proposed removing them. They were removed twice, and the census is what shows
both:

All three rows are **hand-measured, on 2026-09-11**, and they are a history rather than a
measurement of anything that exists now: the first two figures cannot be re-measured without
reverting two repairs. The live figure is the one in the generated census above, and if the last row
disagrees with it, the last row is the stale one.

| | total | reflexivity |
|---|---|---|
| before either repair | 209386 | 90k, 43% |
| after the rewriter stopped proving it had done nothing | 153953 | 46k, 30% |
| after the leaves stopped being built once per use | 122862 | 15385, 12.5% |

**The sentence above carried two figures of its own until 2026-09-14, and they are removed rather
than reconciled.** It said the share was 34.5% over this corpus, and between 33% and 39% over four
hand-picked workloads. The first disagreed with the table's own 43% for the state it described, and
neither carried a date or named a run, so a reader meeting them three lines above a table that does
both had two answers to one question and nothing to choose between them. Which of the two was right
is not recoverable and is not the point: this document's own policy section says an inference count
quoted in prose is spelled from the code where a test names the sentence and carries its date
everywhere else, and a figure that does neither is the kind this file exists to keep out of its own
prose. The four workloads were named nowhere, so that range was never checkable by anyone.

The first repair took the rewriter's idle steps, and with them the congruence and the transitivity
that existed only to carry them. The second is smaller to describe and nearly as large: a proof is a
graph shared by reference, and that was true of everything except its leaves, where `|- = = =` was
built thirty-one thousand times over the library's own lemmas. `Conv.refl` holds the reflexivity of
an atom, so the leaf is one node rather than one node per use.

What is left is structural and will stay: a congruence needs an equation on both sides, and the side
that did not change is a reflexivity that is doing work. `CostCorpusSpec` guards it from above now
rather than from below, because the claim it was pinning has been settled and what is worth catching
is reflexivity climbing back.

### Track K, measured

The corpus is this repository's own, which makes it a different kind of measurement from the ones
below it: nobody else wrote these cases, so the score says what has been thought of rather than how
much of a field's standard set is passed. It is reported for what it is.

| | |
|---|---|
| attacks | 20 |
| defects they are drawn from | 5 |
| must be refused | 15 |
| must be taken | 2 |
| get through, and are recorded limits | 3 |
| came out otherwise | 0 |

These six figures are read out of the corpus by the suite itself, which prints them in an `info`;
they are copied here by hand and were last copied on 2026-09-12. They said 14, 3, 12, 2 and had no
row for the limits at all until then, which is four stale figures and one missing category found by
`grep` rather than by a test. Binding them to the code is `49e8dab4`, and this table is a third one
of the same kind as the two that card names.

**A row carries the refusal by name, not the fact of one.** A corpus recording only refused-or-taken
passes on a kernel that turns every attack away for the wrong reason, and turning something away for
the wrong reason is what a check that has stopped working looks like from outside. So an entry
expects `NotLocallyClosed` or `TheoremHasHypotheses` and not merely a `Left`.

**The two must-accept rows are what keep the score from being free.** A kernel that refused
everything would pass all twelve of the others, and no assertion anywhere else in that file would
notice. It is the same guard `RingCorpusSpec` has where it checks that most of what is readable is
also certified.

**Four cases from the historical record are named there and not held there**, because their home is
the kernel's own suite, where they are tested as a rule's contract rather than as an attack:
abstraction over a variable free in a hypothesis, `eqMp` between sides that are not the same term,
`instType` under a substitution that could collide, and a definition whose type variables escape. A
second copy of a test is a defect while the two agree, so the corpus names them rather than
repeating them, and a reader of the score is told what the number does not include.

**One of the fourteen was found on 2026-09-10** by the second reading of `Kernel.defineType`, and it
is the only entry so far that was not in the record before the corpus existed: a witness whose
predicate names a constant the theory being extended does not declare. `docs/adr/0006` has it.

**This is not coverage, and the number must not be read as one.** It is the attacks that occurred to
the people who wrote them. The 2026-09-03 defect is the standing evidence for what that is worth: it
survived `docs/architecture.md`, `TrustBoundarySpec`, `IsolationSpec` and 251 tests.

### Track R, measured

The corpus is `MathlibTest/Tactic/Ring/Ring.lean`, the file Mathlib uses to test its own `ring`
tactic, vendored under `third-party/mathlib/` at the commit its notice names and byte-identical to
upstream. It is read, not transcribed. Whoever copies a benchmark across chooses which cases to
carry and how to write them, and both choices flatter the system being measured; the selection
rule here is in `RingCorpusSpec` where it can be read and argued with, and every count below is
produced by the suite that asserts it.

A declaration counts as a question put to RING only when upstream closed it with `ring` or `ring1`
and nothing else. `field_simp; ring` hands `ring` a goal this system was never given, `conv => ring`
hands it a subterm, and `ring!` and `ring_nf` are different tactics with different contracts.

| | |
|---|---|
| declarations in the file | 75 |
| proved by exactly `ring` or `ring1` | 49 |
| read as this arithmetic | 38 |
| not read here | 11 |
| certified by RING | 32 |
| refused as outside the fragment | 3 |
| beyond the numeral bound | 0 |
| in the fragment and unproved | 3 |

The last row is a goal this system can state, can afford, and cannot prove, while another prover's
test suite says it is true. It held two members earlier on 2026-09-09, both the same goal
`x/2 + x/2 = x`, and the list emptied itself rather than being emptied: the suite fails on an entry
that has stopped failing as well as on one that has not.

**Its three members now are the first ones that are not a finding about this prover.** Lines 65, 66
and 70 are `(1/x)^2 = 1/x^2`, that again, and `1/x^2/y = 1/(y * x^2)`, and they became readable the
same evening when the reader learned `⁻¹`. Upstream closes each with plain `ring` and upstream is
right: in Mathlib `⁻¹` is a **total** function with `0⁻¹ = 0`, so `(a * b)⁻¹ = a⁻¹ * b⁻¹` holds
everywhere and the identity needs no hypothesis. Here it is not a theorem. `inv` is the field
axiom's inverse and the theory says nothing whatever about `inv 0`, so at `x = 0` these compare two
terms nobody has constrained. RING is right to refuse them, and `Field` proves all three assuming
that a variable is not zero, which track F asserts. The entry records a difference between two
theories, and closing it is a decision about this one rather than a tactic to write.

**That decision was taken on 2026-09-10, and it removes the question instead of answering it.**
`docs/adr/0007` has it: the reals are to be constructed, so `inv` becomes a defined constant and
whether `inv 0` is zero becomes a choice inside a definition rather than a seventeenth axiom. The
comparison that decided it is worth keeping here, because this table invites it. Mathlib does not
have `0⁻¹ = 0` for free either: it is a field of the `GroupWithZero` class, so an axiom there too,
and the difference is that this system counts its axioms in one place and publishes the number.
HOL Light proves it, because HOL Light constructs. Until the construction reaches this far, these
three stay in the row above.

The other rows say where the distance is, and it is not mostly in the prover. The eleven not read
are written with `•`, `↑`, a lambda, or a type ascription that could be a coercion: that is the
width of the reader, which is deliberately narrow, because reading `(n : ℝ)` where `n : ℕ` as `n`
would have the kernel certify a true theorem about a statement nobody wrote. The three still
refused are exponents with a variable in them, which wait on the naturals rather than on RING.

**Six of the seventeen that were unreadable left on 2026-09-09**, when `LeanSyntax` learned `⁻¹`.
It reads as `1 / x` rather than as `x ^ -1`, and the difference decides whether it lands inside the
fragment: a negative exponent is refused by `Translate`, a quotient is not. Three of the six are
certified and three are the unproved row above, which is the bucket a reader wants a newly readable
goal to land in.

**The counts moved three times, and every number is worth keeping.** The third move is the second
half of 2026-09-09: a coefficient in the normal form became a rational number rather than a whole
one, `x/2 + x/2 = x` went from stated-and-unproved to certified, and certified went 27 to 29 while
the unproved row went 2 to 0.

**The second move is the same day and is the larger one.** `Translate` learned to read a quotient,
and the seven quotients that had been sitting in "outside the fragment" left it. Six became
certificates, one became the two members the unproved row then held. Certified went 21 to 27 and
refused went 10 to 3.

That move is worth reading twice, because the refusal had been correct in form and wrong in
substance for as long as the corpus has been measured. `x / y` abbreviates `x * inv y`, and
unfolding an abbreviation asks for nothing; what asks for `~(y = 0)` is cancelling `y` against
`inv y`, which is a different step and belongs to the tactic. One sentence covered both, so the
reader refused the unfolding for the cancellation's reason, and seven goals were held out by an
argument that was never about them.

**The first move.** Measured on 2026-09-04 they were 18
certified and 13 refused; on the same day `Translate` was changed to evaluate an exponent with no
variable in it, and they became 21 and 10. The three that moved were `x ^ (2 + 2)`, twice, and
`(X^5 + 1) * (X^2^3 + X) = X^13 + X^8 + X^6 + X`, whose `2^3` is closed as well. None of them was a
limit of the theory: the border was deciding whether an exponent was a numeral by how it had been
written. The rule now is that an exponent with no variable is computed, exactly, by a function in
`Translate` that is not the simplifier, and the reasoning for keeping those apart is in that file.

**The bound row was 1 and is now 0, and the goal that moved is the whole story of one change.**
`(876544 : ℤ) * -1 + (1000000 - 123456) = 0` is inside the fragment and Mathlib's `ring` closes it
immediately; here it was unreachable, because RING expanded a coefficient of `n` into `n` copies of
a term. Since 2026-09-04 it collects them instead, and this goal is certified. It was one goal
rather than a class only because the corpus happens to hold one six-digit arithmetic identity, so
what the row measured was the frontier and not the corpus; the frontier is now the arithmetic on
the numerals, and `Oracle.NumeralBudget` carries the measurement that placed it at twelve digits.

The whole test costs a second or two, and one goal is most of it: on 2026-09-04, warm,
`(x + 1) ^ 6 = (1 + x) ^ 6` took 1033 ms of a 1055 ms total in one run and 2033 of 2195 in another,
because its expansion carries the coefficient 20 although nothing written in it exceeds 6. Read
those as orders of magnitude and not as measurements: the same ladder run twice on the same machine
the same afternoon differed by about a factor of two, so what the numbers establish is that one
goal dominates and why, which is the same lesson as the paragraph under the ladder arriving from
the other direction.

An earlier measurement of this file, taken on 2026-09-04 by transcribing goals by hand, reported
twenty-one goals surviving a filter and fourteen certified. Those numbers are superseded rather
than corrected: the hand-copied set both missed cases and carried the same goal more than once,
which is the failure mode that made reading the file the design.

### Track L, measured

The corpus is `MathlibTest/Tactic/Linarith/Basic.lean`, the file Mathlib uses to test its own
`linarith` tactic, vendored under `third-party/mathlib/` at the same commit as the ring corpus and
byte-identical to upstream. Read, not transcribed, for the reason track R gives, and every count
below is produced by `LinarithCorpusSpec`.

A declaration counts as a question put to LINARITH only when upstream closed it with `linarith` and
nothing else. `nlinarith` and `polyrith` are different tactics; `linarith [h]` with extra terms and
`linarith` after a preprocessing step hand it a context this system was never given.

| | |
|---|---|
| declarations in the file | 149 |
| closed by exactly `linarith` | 69 |
| about the naturals or the integers | 24 |
| not read here | 11 |
| refused as outside the fragment | 0 |
| read, and not linear | 2 |
| proved by LINARITH | 32 |
| linear and unproved | 0 |

The last row is the same shape as track R's: a member of it is a goal this system can state, is
linear, and cannot prove, while another prover's test suite says it is true. **It is empty, and it
emptied itself twice on 2026-09-09**, which is what the exception list beside it is for: the suite
fails on an entry that has stopped failing as well as on one that has not.

The first was `ε/3 + ε/3 + ε/3 = ε`. The second is the one worth reading. Four goals arrived in the
row the moment LINARITH's reader widened — lines 97, 99, 101 and 105, `0 < x/(-1)`, `0 < x/(-2)`,
`0 < x/(-4/5)` and `0 < x/(2/3)` — and they were not a limit of LINARITH at all: the search found
every certificate and **RING refused to check it**, because RING read `inv <numeral>` as a rational
coefficient and read nothing else that way, so `inv (-1)` and `inv (2 * inv 3)` stayed atoms.
Measured against `Ring` directly rather than inferred. `Coefficient.inverseOfUnit` is what closed
it: `x * y = 1` implies `inv x = y`, so a factor of one cannot be zero and the side condition
`MUL_INVERSE` carries is discharged by the arithmetic instead of by the order — which matters,
because discharging it by the order would have wanted `0 < inv d` below the ring, and the order is
built on top of the ring.

**That limit of RING was invisible until this reader got wide enough to hand it those goals.** The
corpus found a defect in a tactic it was not measuring, which is the argument for reading a corpus
rather than transcribing examples, arriving from a direction nobody planned.

**The distance is almost entirely the theory rather than the procedure, and the largest bucket is
the honest one.** Twenty-four of the sixty-nine are about `ℕ` or `ℤ`, and they are not attempted,
because over the integers `x < y` gives `x + 1 <= y` and that is false over the reals: reading such
a goal here would be reading a different statement, which is the failure `Translate` exists to
prevent one level down. Two are not linear, and that bucket is attempted and refused rather than
skipped: LINARITH multiplies its hypotheses in pairs when the linear search fails, so a non-variable
atom no longer puts a goal outside the procedure by construction, and a suite that went on skipping
them would have hidden the seven it can now decide.

**Proved went twenty-five to thirty-two on 2026-09-10, over three changes, and every one of them
was a defect rather than a capability.** They arrived from a consumer using the procedure on a real
development rather than from reading the code, which is the second time that has been the source.

1. **A product of unknowns was read as one atom, and a manufactured one was multiplied out.** So
   `0 < p /\ d < q ==> 0 < p * (q - d)` was refused while `0 < p /\ d < q ==> 0 < p * q - p * d`
   was proved: the pair of hypotheses multiplied gives a fact over the atoms `p * q` and `p * d`,
   and a goal whose only atom is `p * (q - d)` shares no column with it. Two statements of one
   thing, and whether the author had distributed by hand decided which one the procedure met. The
   reading now goes through the same `Form.times` the manufacturing does, so the two cannot drift.
2. **The products were formed over the hypotheses alone and not over the hypotheses with the goal's
   negation.** That is what `nlinarith` multiplies over, and it puts a whole family out of reach for
   a reason that has nothing to do with the family: from `n * d = b` with `n` and `b` positive it
   does not follow *linearly* that `d` is positive, and it follows at once from `d <= 0`, which is
   the thing nobody had assumed. The negation is not taken by a classical step and there is none
   here to take: `LT_TOTAL` is one of the sixteen, and each of its three cases is an ordinary run
   with one more fact.
3. **An equality took part in no product, on an argument that is wrong.** It said: the difference an
   equality states is zero, so every product with it is zero and carries nothing. The first half is
   true and the second does not follow. `d = 0` times `0 < n` is `n * d = 0`, which is zero and
   which says that the *atom* `n * d` is zero, and the linear reading did not know that. An equality
   is now paired through `a <= b` and `b <= a`, by a lemma that already existed.

**The pair of non-strict kinds became available on 2026-09-10 too and moved nothing by itself.**
`Order.MUL_NONNEG_BOTH` is `0 <= x ==> 0 <= y ==> 0 <= x * y`, which is what LINARITH was missing to
multiply two non-strict facts. Measured after it and before the three above: proved 25, not linear
9, unproved 0, unchanged in every column. It is recorded because the alternative is letting a new
capability be read as a corpus improvement it did not produce, and because a corpus that does not
exercise something is the ordinary reason a gap goes unnoticed rather than evidence there was none.
It is load-bearing now: the equality halves of point 3 are non-strict, and pairing two of them is
exactly what that lemma does.

**Proved went eleven to twenty-two and "not linear" went twenty to ten, over two changes.**
LINARITH's linear form carried whole coefficients until 2026-09-09, so `ε / 3` was an atom and `ε`
was a different one and no combination reached from one to the other. A quotient by a constant is a
coefficient now, and the constant may be negative or a ratio. Nothing on the checking side moved for it: `Farkas` has always solved
over the rationals, a multiplier is still cleared to a whole number before any theorem is built,
and what shows a denominator to the kernel is RING.

**Nothing is refused as outside the fragment any more, and the row above used to hold fifteen.**
All fifteen needed division, and on 2026-09-09 the reader learned to read a quotient. Fourteen of
them turned out to be goals whose atoms LINARITH could not see, which is the "not linear" bucket.
The table above says how many are left in it, and everything that has left it is proved: with
nothing refused as outside the fragment and nothing linear and unproved, a goal leaving that bucket
has nowhere else in the table to go. The outside-the-fragment row did not empty because the
procedure got stronger; it emptied because a refusal that named the reader was replaced by refusals
that name the procedure, which is the more useful of the two and is the whole reason this table
separates them. The eleven unreadable ones are the width of the reader: a decimal literal,
`Set ℕ`, `Nat.prime 7`, and four hypotheses written `¬ b ≥ 0`. `10⁻¹` was among them until the
reader learned `⁻¹` on 2026-09-09, and it is the twenty-third proof in the row above. That last shape is
classically the same as `b < 0` and turning it round would be a semantic step taken in a reader
that is meant to be syntax only, so it stays out.

**`False` as a goal is read, and it is not an exception to that rule.** Six declarations in the
file state `: False` from hypotheses that cannot all hold, and that is the falsity the logic
already has; asking whether the premises imply it is asking whether they can all hold at once,
which is the half of the procedure that has nothing to do with a goal. They were unreadable when
this suite was first run and are proved now.

**Two defects came out of running it, and both were in this repository rather than in the corpus.**
An unreadable hypothesis was being dropped rather than making its declaration unreadable, which
would have counted four goals as failures of the prover when they were failures of the reader; and
a goal that is an equality was not attempted at all. The second is now proved the way Mathlib
proves one, by bounding both ways and appealing to antisymmetry, which `Order` derives.

### Track F, measured

The corpus is track R's file, read twice more and for two different questions. `Field` is `Ring`
plus one step, `d * inv d` becomes `1`, and that step costs a hypothesis, so a tactic that carries
one has two ways of being wrong and only one of them is about proving power.

**What it costs: nothing.** Every goal track R certifies goes through `Field` as well, all of them
come back proved, and **not one of them comes back assuming anything**. That is the
"a condition is assumed only if it was used" property checked against goals a library's users wrote
rather than against one example. It holds for a structural reason — a hypothesis reaches a theorem
only through the inference that used it, so a cancellation rule that never fires contributes none —
and the reason being easy to believe is not the same as the property being measured.

**What it adds on those goals: nothing, and that is the selection rule rather than the tactic.**
Track R counts the declarations upstream closed with `ring` or `ring1` alone, so they are ring
identities by construction and have no denominator to cancel.

**The field goals of that file are the ones track R throws away**, and there are three: the
declarations upstream closed with `field_simp` and then `ring`. Asking `Field` those directly is
the fair question, and a harder one than track R asks, since upstream needed two tactics where this
is one.

| | |
|---|---|
| declarations closed by `field_simp` then `ring` | 3 |
| proved | 3 |
| unreadable | 0 |
| refused as outside the fragment | 0 |
| read, and unproved | 0 |

**All three are proved, and this table read `0 / 2 unreadable / 1 unproved` earlier the same day.**
All three said the same thing then and it had one cause: every one needs the inverse of a *product*
taken apart, `inv (a * b)` into `inv a * inv b`, which `Field` refused by name and documented itself
as refusing. Two were unreadable on top of that, being written with `⁻¹`.

**The lemma that closed it is not the one this document expected**, and the difference is worth the
paragraph. The obvious route to `inv (a * b) = inv a * inv b` derives `~(a * b = 0)` from `~(a = 0)`
and `~(b = 0)`, which is the absence of zero divisors: a real theorem, with a case analysis behind
it, and the fact the rational-coefficient design had gone out of its way to avoid needing.
`Coefficient.inverseOfUnit`, `!x y. x * y = 1 ==> inv x = y`, makes it unnecessary — the product of
the two reciprocals multiplies `a * b` to one by rearranging, and a factor of one is an inverse. So
the two conditions the tactic charges are the two it was already charging for the factors, and
nothing new is assumed.

**A denominator is now taken apart by recursion rather than by a case**, so `inv (24 * x)`,
`inv (-x)` and `inv (inv x)` are one mechanism: each shape says what its reciprocal is, a numeral's
is settled by `Positivity` and costs nothing, and only an atom assumes `~(d = 0)`. That is what
keeps the conditions minimal, and the first version of it did not: splitting only the outermost
product left `inv (x * (x * y))` assuming `~(x * y = 0)` beside the two conditions genuinely needed.
Sound, and a hypothesis a reader has to think about for nothing. `FieldCorpusSpec` now asserts that
every condition names a single variable, which is what catches that.

**The split is the second attempt and not the first**, and the order is what keeps the property
above true. Splitting is an inference like any other, so a rule that fires puts its conditions on
the theorem whether the proof needed them or not: `(z * x) / (2 * y) = z * (x / (2 * y))` is true at
`y = 0` too, and splitting first proved it while assuming `~(y = 0)`. Trying without the split costs
one normalisation on the goals that need it and nothing on the goals that do not.

### Track T, measured

The only way this system can mislead is not a wrong proof. The kernel certifies the inference and
not the translation, so the failure that carries the authority of a proof is a plausible and wrong
*formalisation* followed by a correct proof of it. `Translate` names that danger on the narrow
border it guards, `Expr -> Term`. The border with a sentence in Italian is the same danger with
nothing on it, and this is the corpus for it.

**Traps, not examples.** A set of sentences that formalise correctly measures nothing, because the
failure is not that the obvious reading is hard to find: it is that a wrong reading is obvious. Each
case carries two readings of one sentence, and the question asked of the system is whether it can
show they are different statements.

| | |
|---|---|
| traps | 9 |
| separated by a point where the two disagree | 2 |
| separated by a decision, one proved and one refused | 6 |
| separated by a decision that eliminates the quantifiers | 1 |
| not separated by anything here | 0 |
| proved in the misreading while the faithful reading is refused | 0 |
| printed identically, so a reader has nothing to compare | 0 |

**Three rows are assertions and the rest is the report, and they are named rather than numbered
because this table gained a row on 2026-09-10.** A trap in *proved in the misreading while the
faithful reading is refused* would be this system being misleading rather than merely limited: a
theorem handed over for the question nobody asked, beside a refusal for the question they did,
which is worse than refusing both. One in *printed identically* would mean the surface had failed
before anyone read it. And *not separated by anything here* became an assertion on 2026-09-10, when
the entry the next paragraph is about left it.

**The one it could not separate was the classic one, and it left the list on 2026-09-10.** `Per ogni
valore ce n'è uno più grande` reads as `!x. ?y. x < y`, and swapping the quantifiers gives
`?y. !x. x < y`, which is false over the reals. Until that day nothing here settled either: no
tactic decides a quantified statement, so neither reading was proved, and the sampler declines a
universal premise because there is no finite domain to enumerate. What was left was that the two
print differently and somebody looks, on the failure autoformalisation is most known for.

`Quantified` settles it, and how it settles it is the part to read. It eliminates the quantifiers
over untrusted linear forms and answers whether the claim holds over the reals: **decided, and not
proved.** No theorem is built and none may be read into it, which is why the table gives that row a
line of its own instead of counting it with the six above, where a tactic proved one reading and
refused the other. A refusal is not a disproof and a decision is; they are different evidence and
the report says which it had.

What that costs is the same as what `Refutation` costs, and it is under the same record,
`docs/adr/0005`: a model of the reals answers, and the kernel is not involved. Making the
elimination produce a proof is a different piece of work and a real one, since each step would want
the density and the unboundedness of the order as derived lemmas.

All nine are separated, and the quantifier swap above is the ninth. The eight told apart by a point
or by a proof are a mean read as a sum, "at least" read as "more than", a dropped side condition,
an implication read backwards, percentage points read as per cent, "grown by" read as "grown to",
the mean of two ratios read as the ratio of the sums, and a unit dropped between hours and minutes.
Four of those eight are statable only because a numeral denominator became a coefficient on
2026-09-09: before that the reader refused them and the trap could not be posed.

**No existing benchmark was adopted, and the reason is the first row of this document.** miniF2F,
ProofNet and the autoformalisation sets built on them state their problems over the naturals with
induction, which this theory cannot write at all. A score there would measure the absence of the
naturals, not the quality of a translation, and would read as zero for a reason that has nothing to
do with what is being tested. The corpus is small and it is over the fragment this system has, which
is the only kind that measures anything.

### Track D, measured

Twenty-one candidates carrying their labels, written by hand rather than generated, in three equal
parts. The corpus is balanced by assertion and not by accident: precision and recall over a corpus
that is nine tenths one label are numbers about the corpus.

| | |
|---|---|
| labelled candidates | 21 |
| true and inside the fragment | 7 |
| near-misses, by one coefficient or one sign | 7 |
| true and outside the fragment | 7 |
| near-misses the screen caught | 7 of 7 |
| true identities the screen threw away | 0 |
| certified, of those true and inside | 7 of 7 |
| unsettled | 7, all of them outside the fragment |
| worst agreement of a true candidate, at 50 digits | 49 |
| best agreement of a false candidate, at 50 digits | 9 |

**Precision is the assertion and recall is the report, and they are not symmetric.** A false
candidate that survives the screen costs one certification attempt and then a refusal, which is the
mistake this arrangement is built to absorb. A true one thrown away is gone: nothing downstream sees
it, and the run reports a witness that is really a rounding error. So a true identity coming back
`Disproved` fails the suite, and a near-miss surviving is reported and listed by name.

**The row that used to say 6 of 7 is where the second stage came from.** `x + x / 1000000000`
against `x` is false by one part in a thousand million, which is under `Discovery.Tolerance` of
1e-8. Until 2026-09-11 it passed the whole screen, RING refused it, and it landed in
`NotProvableHere`, the bucket that means a candidate agreed everywhere and did not become a theorem.
That was the loop's argument as a measurement rather than a claim: a screen that reported its
survivors would have called it a discovery.

It is caught now, by the second stage, at the ninth digit, and it comes back `Separated` rather than
`Disproved` because those are different facts about a candidate. `docs/adr/0011` is the decision and
the last two rows of the table are what makes it safe: **every** true candidate agrees to 49 or 50
digits at its worst sampled point and the false one agrees to 9, so the gap the stage is asked to
see is forty digits wide. That margin is the measurement and not the precision by itself, because a
true identity does not agree to every digit: each step of an expression rounds, and `exp(log x)`
against `x` comes back agreeing to 49 of 50.

**Nothing true was thrown away, including the row put there to try.** `(x + 10000)^2 - x^2 -
20000 * x = 100000000` cancels two quantities of about 1e8 down to their difference, which is where
a screen with an absolute tolerance reports a rounding error as a witness. The tolerance is relative
and this is where that choice is measured.

**Writing the sub-tolerance near-miss took a fact worth recording.** It is a quotient by a whole
numeral and not a fractional literal, because `Translate` refuses the second by name: a fractional
`Num` is not a numeral of this theory, whose numerals are integers, while `x / 1000` is read. Written
the other way the candidate would have left the fragment and measured the reader instead of the
screen.

**All seven outside the fragment come back unsettled and say so**, none proved and none disproved.
That is the third of the corpus the loop exists for, and the row a reader most easily misreads:
`Translate` refuses `sin`, `cos` and `exp` by name, so there is nothing here for the kernel to see,
and counting these as failures to certify would say the loop proved a third less than it did.

### What a corpus is believed on, measured

The first bullet of the list above measures one theorem. This measures a corpus, and it is the
question a prover has never been able to answer about a body of work: not how much of it went
through, but which of the things anyone was asked to believe actually took part.

`Cost` in `modules/tactics` asks the five questions at once and keeps their answers apart, and
`CostCorpusSpec` runs it over track R's file. Frozen at the commit `RingCorpusSpec`'s notice names,
measured on 2026-09-10.

| | |
|---|---|
| declarations in the file | 75 |
| goals that read as propositions here | 46 |
| proved outright, nothing owed | 37 |
| proved at a price, the price named | 6 |
| decided false, with the point | 2 |
| neither, with the point | 1 |
| axioms the corpus reaches, of sixteen | 15 |
| axioms a single proof reaches | 1 least, 8 median, 15 most |
| inferences, all proofs together | 122862 |

**Completeness is the one never reached**, by any proof in the file. A corpus about polynomial
identities never asks for the axiom that makes these the reals rather than the rationals, and every
other axiom takes part somewhere. Nothing about that is surprising; the point is that it is a
measurement and not an assumption, and that no prover this document compares against can produce
the same line for its own corpus.

**Six goals are identities upstream and identities at a price here**, and the difference is between
two theories rather than a shortfall in one. Mathlib's inverse is total, `0⁻¹ = 0`, and this one is
not, so `1 / x * (1 / x) = 1 / (x * x)` holds everywhere there and away from zero here. What makes
that visible is the condition coming back in the sequent instead of being absorbed into a refusal:
the three distinct conditions over the six goals are `~(x = 0)`, `~(y = 0)` and `~(z = 0)`, one per
variable and never a compound, which is the property track F's table is about.

**The three that do not close are not this system falling short**, and checking that was the useful
part of the measurement. Two are stated upstream with a hypothesis the extraction drops, so what
was asked here is a different and false claim: `x = 0` under `h : x - x + x = 0`, and `A * B = 2`
under `H : B * A = 2`. The third, `a - b - c - d = 0`, is closed upstream with `test_sorry` and is a
trace test for the normaliser rather than a theorem. All three come back with the point they fail
at, which a reader checks without trusting anything here, and the false one Mathlib leaves open is
refuted rather than merely refused.

**The spread of the axiom reach is the part a single figure would destroy.** Ten proofs rest on one
axiom and seven on fifteen, and the difference is what the proof had to do: ten of them are lookups
in a library rather than derivations, a proof that only rearranges a sum touches the ring axioms,
and a proof that divides by twenty-four asks the order whether twenty-four is positive. A
corpus-level count of fifteen says what the theory permits; the spread says what each proof cost.

The floor row and the least column both moved on 2026-09-11 and neither for the same reason, which
is why they are separate rows: the least came down when `Prove` began asking its library first, and
the total came down when the rewriter stopped building a theorem to say it had done nothing.

**122862 inferences is what a second checker has to replay**, and is the figure track R' is measured
against. It did not exist before a theorem recorded its derivation, and neither did any of the rows
above.

### The ladder, measured

Two columns since 2026-09-04, because RING has two normal forms and a change measured only on the
side it improved is not measured. **Expanding** unfolds the binary numerals, so a coefficient of `k`
becomes `k` copies of the term; **collecting** keeps it a numeral and does the arithmetic on it in
binary. `Ring.standard` is the second; `Ring.expanding` is the first and is what proves the lemmas
the second runs on.

| Goal | Expanding | Collecting | Result |
|---|---|---|---|
| `(x + y) * (x + y) = x * x + 2 * (x * y) + y * y` | 3 ms | 4 ms | proved |
| `(x + 1)^5`, expanded | 219 ms | 11 ms | proved |
| `10 * x + 10 * x = 20 * x` | 10 ms | 1 ms | proved |
| `50 * x + 50 * x = 100 * x` | 392 ms | 2 ms | proved |
| `12 * 12 = 144` through RING | 957 ms | 1 ms | proved |
| `1000 * x + 1000 * x = 2000 * x` | not run | 6 ms | proved |
| `876544 * -1 + (1000000 - 123456) = 0` | not run | 10 ms | proved |
| `x + x = 3 * x`, which is false | 3 ms | 2 ms | refused |
| `x < y /\ y < z ==> x < z` through LINARITH | 4 ms | proved |
| `2 * x < 2 * y ==> x < y` through LINARITH | 6 ms | proved |
| `3 * x < 2 * y /\ 2 * y < 5 * x ==> 0 < x` through LINARITH | 5 ms | proved |
| `x < x + 1` through LINARITH | 1 ms | proved |

The two "not run" cells are the point of the change rather than a gap in the measurement: the
expanding form would spend minutes on them, which is what the row above them is evidence for. The
LINARITH rows are new on 2026-09-05: the second was a refusal in every earlier version of this
document, and the next section is what changed.

**Every number in that table is soft, and by more than the last version of this section admitted.**
Measured the same afternoon on the same machine, `Arithmetic.multiply(999, 999)` took 459 ms on the
first call and 8 ms warm, a factor of fifty-seven; the ladder above is the warm figure throughout.
An earlier version of this table recorded 115 ms for that goal and 18 ms for `12 * 12` through
ARITHMETIC, and neither was wrong when it was taken. This is the reason the assertions live in
`RingCostSpec` as node counts and the times are reported beside them.

**What drove the cost in the expanding form was the largest numeral in the simplified form, not
the shape of the input.** It expands a numeral into that many copies of the term, so `-3^2^2`,
seven characters, costs what its simplified form `-81` costs: in a warmed run of forty generated
expressions at depth 2 with coefficients within ±3, measured on 2026-09-04 while
`OracleCertificationSpec` was written, that one expression took 424 ms of a 476 ms total, and five
took under a millisecond. The distribution was heavy-tailed enough that a mean per expression was
the wrong statistic, and a table indexed by depth and coefficient size would have taught the wrong
lesson: depth and coefficients mattered only through the probability that they produced a large
numeral, which exponentiation does without anyone writing one down. That same run costs 48 ms
through the collecting form, and the expression that dominated it no longer does.

The ladder is a machine on a day. The cause underneath it is not, and both causes are asserted
rather than described, in `RingCostSpec`, one per form:

| | Expanding | Collecting |
|---|---|---|
| normal form of `k * x` | `4k - 3` nodes | `2 * bits(k) + 3` nodes |
| normal form of `(x + 1)^k` | `k * 2^(k+1) + 1` nodes | `k + 1` monomials |
| at degree six | 769 nodes | 133 nodes |
| at degree twelve | 98305 nodes | 507 nodes, 143 ms |
| `12 * 12` | 573 nodes | the numeral `144`, 15 nodes |

The left column follows the **value** of the coefficient and the right follows the number of digits
it is written with, which is the size of the input. That difference is the whole change, and it is
why `1000 * x`, which this document called out of reach, is now six milliseconds.

Two things the ladder still says. A numeral product through the expanding form costs several
hundred times what the dedicated numeral procedure costs, which is why a tactic dispatcher that
tries ARITHMETIC first is a twenty-line pattern match and not a model; through the collecting form
it costs the same as that procedure, because it is that procedure. And the LINARITH rows are no
longer a limit: what they used to record is in the section below.

### The certificate search, measured

Until 2026-09-05 the search enumerated the subsets of the hypotheses and took the first whose sum
was the goal, so every hypothesis was used once or not at all. That decided the goals that happen
to be a plain sum and refused the rest, and it cost what enumerating subsets costs. It is now a
linear program over the rationals: the goal follows exactly when its difference is a non-negative
combination of the hypotheses' differences plus a non-negative constant, or when the hypotheses
contradict each other, and phase one of the simplex answers both.

Two things changed, and they are different kinds of thing. The first is what can be proved, and it
is not a speed-up: `2 * x < 2 * y ==> x < y` needs the multiplier one half and was outside the
procedure at any budget. The second is the cost, and it is measured against the old search rather
than argued, by running both over the same forms on 2026-09-05. The shape is `n` hypotheses of
which two are needed, which is where an enumeration is worst, because the pair it wants is the last
subset it reaches:

| Hypotheses, two of them needed | Subset enumeration | Certificate |
|---|---|---|
| 4 | 14 ms | 25 ms |
| 8 | 46 ms | 1 ms |
| 12 | 134 ms | 1 ms |
| 16 | 1138 ms | 1 ms |
| 20 | 27669 ms | 7 ms |

The first row is the honest one to keep: on four hypotheses the old search wins, because the
simplex is a tableau of exact rationals and that is the cost of the first call. By eight it is
already behind, and the last row is a factor of four thousand. A chain of hypotheses where all of
them are needed is the enumeration's best case and stays cheap in both; the new search does a
chain of sixty-four in 110 ms.

What the multipliers cost the kernel is a different number and a small one. A certificate is
cleared of its denominators, so the theorem is built from whole multiples: each one needs `0 < k`
for a numeral `k`, which is a derivation per bit, and the common denominator comes off at the end
through `Order.cancelPositive`. `1000000 * x < 1000000 * y ==> x < y` is 6 ms, the same as at a
coefficient of two, because what the numeral costs follows its digits.

**The products of the hypotheses, measured on 2026-09-09.** Since that day a goal the linear search
refuses is tried again with every pair of hypotheses multiplied, itself included, which is the move
`nlinarith` makes over `linarith`. The pairs are quadratic, so what it costs is worth stating as two
numbers rather than one: what a goal that never needed them pays, and what a refusal pays.

| Hypotheses in a chain | Decided linearly | Refused, with the products built and searched |
|---|---|---|
| 2 | 2 ms | 21 ms |
| 4 | 3 ms | 16 ms |
| 6 | 3 ms | 26 ms |
| 8 | 4 ms | 36 ms |
| 10 | 5 ms | 48 ms |
| 12 | 5 ms | 67 ms |

The left column is the answer to the question the order was chosen for: a goal that is decided
without the products costs what it cost before, because they are never built. The right column is
what a refusal costs at ten hypotheses, which is the size of a real goal. On the goals that need
them the products are cheap, because the certificate is found immediately once the atom exists:
`0 < x /\ 0 < y ==> 0 < x * y` is 1 ms and the same goal among four hypotheses is 3 ms.

**The right column doubled on 2026-09-10 and could have gone up a hundredfold.** Two things landed
that a refusal pays for: the three cases of the goal's negation, each of which may build the
products again, and a second round of products at degree three. Ungated, the second round took a
refusal on twelve hypotheses from 32 ms to **2918 ms**, which is the measurement that decided the
design rather than a number recorded afterwards.

What made it payable is a gate that is about the goal rather than about a budget: **the round runs
only when the goal names an atom neither the hypotheses nor their pairwise products reach.** A
certificate is a combination over columns, so an atom nothing else mentions is a column that can
only be weighed zero, and a chain of linear hypotheses names none — it never builds a cube and pays
67 ms instead of 2918. A goal writing `r * e * d` names one, since no pair of three hypotheses
makes a product of three factors, and it gets the round. The candidates are judged by the form they
would have, computed without deriving anything, so the filter costs less than the theorems it
avoids building.

Read these as orders of magnitude like everything else in this section. What they establish is the
shape: the common case is unchanged and the cost lands on the refusal.

The same day the fragment widened to the shapes a corpus of measurements is actually written in: a
hypothesis may be `a <= b` or `a = b`, and the conclusion may be `a <= b`. An equality is weighed
with either sign, since what its multiplier multiplies is zero. The one thing that needed care is
that a combination weighing only non-strict facts proves nothing strict, so the search has a second
phase that asks for a point where some strict fact carries weight; `x <= y ==> x < y` is refused,
which is the assertion that pins it.

## The exposure of the trusted base, and what the line count does not measure

The project publishes one number about its trusted base: four files under 1200 lines, with a test
that measures it and a record for every time the bound moved. What it has never published, and had
no way to say, is **how much hostile attention those lines have had**.

**The line count measures readability, not verification, and the two are different properties.**
"Small enough that somebody could read it" is strictly weaker than "proved correct", and the
comparators that occupy the second niche are available to the same reader: Candle is a HOL kernel
verified down to machine code through CakeML, and the Metamath verifiers are small enough to have
been written many times over and cross-checked against each other. HOL Light's kernel is about 450
lines and has had thirty years of people trying to break it, plus a self-verification result. Those
are not the same kind of claim as this one and this document should not put them on one axis.

### What the exposure actually is

Hand-maintained, on purpose: there is no way to measure it from the code, and a table that admits
being a photograph is better than a number that pretends not to be.

| Pass | Date | Who, and with what intent | In the trusted base | Outside it |
|---|---|---|---|---|
| The binder representation, read to break it | 2026-09-03 | an adversarial audit | **1, unsound**: capture through `inst` and `abs`, live at the time | |
| `defineType`, read again by the model that wrote it | 2026-09-10 | checking a new rule against Harrison | **2**: a witness holding hypotheses, a witness naming another signature | |
| Ten dimensions, each with its own reason to open the files | 2026-09-10 | finding what is missing against Lean 4 | **3 soundness-relevant, 1 more as a hypothesis**: `Term.abs` without its closedness check, the constant-identity question, the checker saying yes to `\|- F`, and the signature invariant | |
| Somebody else's benchmark, read rather than transcribed | 2026-09-11 | measuring reach on miniF2F | 0 | **2**: three true theorems decided false, and a 439-second refusal |
| A trap corpus for the naturals | 2026-09-11 | measuring what separates two readings | 0 | **1**: the chain did not build `Peano`, so the arithmetic on `num` was unreachable |
| Reading miniF2F again, with the naturals translatable | 2026-09-11 | widening `Translate` to a second type | 0 | **2**: `Abduce` read "not decided" as "satisfiable" on 65% of what it reported, and the corpus reader defaulted an unknown binder type to `real` |
| The trusted base read to break it, after a day spent inside it for other reasons | 2026-09-11 | the card that says a pass finding zero is weak evidence and three are not | **1**: the argument for the boundary claims more than the boundary does | **1**: the second checker accepted an axiom no theory asserts |
| `defineType` and the work standing in the verification station, read to close it | 2026-09-14, 2026-09-15 and 2026-09-16 | three passes over cards awaiting verification, the last with the whole suite green on a clean tree at `d0dde93` rather than a static reading | 0 | **1**: a docstring in `LauncherSpec` claiming a suite in a file not ending `Spec.scala`, which the rename in an ancestor commit had already removed |

### What the sixth pass found, since neither of its two findings is a wrong inference

Nothing in the ten rules moved, and that is the third pass in a row to say so. What moved is the
**argument**, in the one place it claimed more than it could.

`Kernel.Thm` became a class rather than an opaque type on 2026-09-10 because an opaque type erases
and `(Nil, p).asInstanceOf[Kernel.Thm]` produced a theorem out of a pair. The note recording that
went on to say the boundary is now "enforced by the runtime rather than by the compiler alone, which
is the difference between a wall and a convention". The runtime enforces the **type**, which is why
the cast throws. It does not enforce the **construction**: `private[Kernel]` is a Scala access rule
and the constructor it compiles to is `public` in the bytecode, so a caller using reflection makes a
theorem with no cast, no access check and nothing raised. `TrustBoundaryTwinSpec` asserts both
halves now instead of describing one.

That is a limit rather than a hole, and it is worth the distinction: nothing in ordinary Scala
reaches it. What matters is what lies past it, and the answer is not the kernel. A forged theorem
carries a derivation, and `modules/checker` re-reads it: a derivation that does not add up is
refused, which is what happened to the first forgery tried. **The second forgery added up.** A
derivation that says `Axiom(F)` is a well-formed axiom step — a closed proposition standing alone —
and the checker accepted it and reported `F` among the axioms, where every test in this repository
read the count and not the contents.

The file's own note said it "cannot check an axiom", and that is true of an axiom's **truth** and
false of its **membership**. `Check.proof` and `Check.table` take the theory now and refuse an axiom
it does not assert. The repair has a second use that was not the reason for it: checking the
naturals' facts against the theory of the reals is refused, correctly, because they rest on choice
and on infinity and that theory asserts neither. "Is this a proof" and "is this a proof **here**"
had been one question.

The datum is not the defects. **The datum is the rate**, and it is the only evidence this repository
has ever had about the soundness of its base. Two things follow from the table as it stands.

The first is that a reading with a *reason of its own* finds things, and six of the seven rows are
one: somebody wanting to state a benchmark, to separate two readings of a sentence, to compare
against another system. **The seventh is the exception and it is the informative one.** It was read
for no other purpose, it is the pass the paragraph below used to be waiting for, and what it found
was not in the ten rules: it was that the argument *about* the rules claimed more than they do, and
that the second checker accepted an axiom no theory asserts.

The second is the cadence. **The adversarial reading is redone, and the count per pass is the
measurement.** Three consecutive passes have now found nothing in the ten rules, and the third of
them went looking. That is the first evidence of the kind this section was waiting for, and it is
weaker than the plain count suggests in one direction and stronger in another: weaker because two of
the three were reading for something else, stronger because the one that was not still moved nothing
in the rules. What it moved was the sentence describing them, which is the failure this whole
document is arranged against and is why the row is in the table at its own count rather than at
zero. The honest statement remains the one at the top of this section: the base is small enough to
read, and it has been read by its authors, for ten months, a substantial part of that by a model
checking its own work. `docs/adr/0006` says the same thing about one rule and calls the debt by its
name.

**This paragraph was written in the future tense and stayed there after the pass it describes had
landed in the table above it**, saying "if the next pass finds nothing" and "the last two rows found
nothing in the kernel" when the last row found one. Corrected on 2026-09-15 by the sweep over the
closed cards, which is the only thing that read the prose against the table it sits under. Nothing
fails when these two go out of step, and the section immediately below is about exactly that
distinction.

## Which figures here are alive, and which are a photograph

Every number in these documents is one of two things and a reader cannot tell them apart by
looking, so this says which is which. The distinction matters because the ones in the second column
**will** be wrong eventually: the axiom counts moved twice on 2026-09-10 alone.

| Figure | How it is kept |
|---|---|
| The second reading, the serialised figures and the ring corpus census | **Generated by** `sbt "tactics/Test/runMain garden.xeno.symbolum.tactics.Evaluation"` and compared against the live measurement by `FiguresSpec`, which fails naming that command. The three tables carry their markers in this file |
| The six classical statements, in `proving.md` | Generated by `sbt "theories/runMain garden.xeno.symbolum.theories.Guide"` and compared by `GuideSpec`. It was a hand copy in two places until 2026-09-12, and both were stale |
| `12 * 12 = 144`, wherever a sentence quotes it | Spelled out of the proof by `FiguresSpec`, in this document and in `architecture.md`. The classical step counts quoted in prose are spelled the same way by `ClassicalSpec`, in `proving.md`, in `CLAUDE.md` and in `Classical.scala` and `Logic.scala` |
| The axiom counts, per theory and per chain | Asserted from the live theory. `DocumentationSpec` spells the number out of `Real.Axioms.length` and `Classical.Axioms.length` rather than matching the literal, so the document and the code cannot disagree in either direction |
| The trusted-base line bound | Asserted from the bound, and the claim in both documents is spelled from it |
| The classification of every kernel file | Asserted: a new file in the directory fails the suite until it is put in one of the two lists |
| Track R's and track L's corpus tables | Asserted by the suites that produce them, row by row |
| Track M's counts and its blocking histogram | Produced by `ReachSpec`, which asserts the buckets sum to the file and prints the histogram; the numbers here are copied from a run and carry its date, so they are a photograph of a live measurement |
| The rendered `Cost` report in `proving.md` | Asserted line for line, inference count included |
| Every named lemma, in `lemmas.md` | Asserted: a lemma the library holds and the document does not fails the suite |
| The examples in `proving.md` and the README | Executed |
| **Timings** | Hand-measured, on the date each section names, on one machine, single runs. Read as orders of magnitude. The same ladder differed by a factor of two on one afternoon |
| **Inference counts quoted in prose** | Spelled from the code where a test names the sentence — the rows above say which — and hand-measured on the date given everywhere else |
| **Proof sizes and memory figures** | Hand-measured |
| **Figures inside `docs/adr/`** | A photograph of the date the decision carries, by construction: a decision record says what was true when it was accepted and is not maintained afterwards. Where one of its figures is still live, the document that owns it is the one to read |
| **Test and coverage counts in commit messages** | A photograph of that commit, and not maintained afterwards |
| **The exposure table** | Hand-maintained, and it says so in its own section: there is nothing in the code to measure it from. A pass that is not added to it did not happen as far as this document is concerned |

The rule the second column follows: **a number without a test that ties it to the code is a number
that will be wrong**, and it is written with its date so that a reader can weigh it. A number in the
first column has no date because it does not need one.

## Where a language model fits

Ranked by what it is worth today against what it costs, and the column that matters is whether
the kernel catches a wrong answer. Where it does, the model can be turned loose and the worst
outcome is a `Left`. Where it does not, the model is deciding what is asserted, and nothing
downstream can tell.

| Where | What the model does | Kernel catches a wrong answer? | Worth today |
|---|---|---|---|
| New derivations in `Arithmetic`, in the style of the hand proofs there | writes the derivation of a lemma whose statement a person wrote | **Yes**, provided the test compares the conclusion with the statement as written and not only `isRight` | high |
| RING with collected coefficients | writes the alternative normal form and its lemmas | **Yes.** A wrong normaliser gives a refusal or a slower proof, never a false theorem | done for whole coefficients on 2026-09-04, and the prediction held: the two defects found on the way were a mis-chained congruence and a type error, both of which the compiler or a failed proof reported at once |
| LINARITH: what is left past the products | the linear fragment is decided as of 2026-09-05, the pairs reach past it as of 2026-09-09, and a second round reaches degree three as of 2026-09-10; degree four is not something the search can guess, and since 2026-09-18 it is not what is wanted either: `docs/adr/0032` measured that the two corpus goals asking for more have **no hypotheses at all**, so the pool the products are built from is empty and no degree of them exists, and what they needed was a completed square | **Yes** for the search. **One hole:** a model that reaches for `assertAxiom` instead of deriving an order fact grows the trusted base silently; `RealSpec` scans the sources for exactly that | medium |
| The Collatz re-derivation, and any statement the owner wants formalised | diagnosis, transcription, variation | **No.** The integer screen checks falsity; nothing checks truth, and the kernel cannot state it | high, as a reader |
| The rewrite rule pool in `Rewrite` | chooses which proved theorems enter the set, and their order | **Yes**, structurally: a rule can only be built from a theorem. Divergence is bounded by the step limit, which today ends silently | low |
| `Oracle.certifyIdentity` | proposes a right-hand side, as a second oracle beside the algebra system | **Yes.** Outside the fragment is refused by name; inside, RING certifies or refuses | low |
| New rules in the algebra system's simplifier | writes simplification and expansion rules | **Yes** for polynomials with whole coefficients; **no** for anything with `sin`, `cos`, `exp`, `log` or division, which is most of what the algebra system is for | medium |
| A tactic dispatcher | picks which tactic to try | yes, and pointless: a pattern match beats a model on latency, cost and determinism | none |
| `Discovery.identities`, the candidate list | generates candidate expressions | **No on two of three branches.** `Proved` is checked; `Disproved` is double arithmetic, reached first; `Unsettled` is the absence of a proof, and now says which of four absences | low, see below |
| `Real.Axioms`, `Real.Definitions`, the notation | proposes an axiom, a definition body, a notation declaration | **No. Nothing checks any of these.** `assertAxiom` checks well-typedness and nothing else; `defineConstant` checks conservativity and nothing about meaning; the notation decides what every axiom string means | none |
| `modules/kernel` | writes trusted-base code | **No, and the failure is silent, permanent and retroactive** | do not |

### The unguarded slots, stated plainly

These are the only ways adding a model can make the system unsound. Everything else costs a
refusal and no theorem.

1. **A new or edited axiom.** Nothing checks truth. `0 < 1`, the tempting one, is a theorem of an
   ordered field, so asserting it would be precisely the error this slot exists to prevent.
2. **A definition body.** Consistency-safe and meaning-unsafe: `sub x y = x + y` yields a
   consistent theory in which every theorem printed with `-` is about addition, and RING still
   certifies.
3. **Notation.** A precedence change silently alters which proposition an axiom string denotes.
   The axiom stays well-typed and the build stays green.
4. **The goal string.** The kernel faithfully certifies a correct proof of the wrong theorem.

Both soundness defects found in this repository during the 2026-09-03 audit were put there by
people, in exactly these places, and stayed green through six hundred tests. That is the argument
for the placement above, and it is not caution.

## The conjecture hypothesis, judged

The hypothesis: a model is most useful for producing conjectures, because generation is cheap and
verification is automatic, so cheap screening plus a certifying kernel changes the economics of
discovery.

The general claim is defensible, and it is the FunSearch and Ramanujan-Library recipe. The
specific application to this system, today, is not, for three reasons that are properties of the
system and not of models.

1. **The fragment that gets certified is decidable and exhausted.** RING is a complete decision
   procedure for polynomial identities. Anything it certifies was computable by expansion before
   the model was involved, so "survived screening and got certified" carries no information about
   novelty. The expected number of new theorems from this loop is zero, not small.
2. **Everything interesting lands in the bucket with no check**, and the evidence behind it is now
   worth something. `Translate` refuses `cos`, `sin`, `exp`, `log`, division and large exponents by
   name, so every transcendental candidate is unsettled by construction. What that bucket rested on
   used to be agreement to eight digits at the sample points, and the sentence here said that
   experimental mathematics screens at hundreds of digits and that eight cannot tell a near-identity
   from a discovery. That was true and it has been answered: since 2026-09-11 the screen's second
   stage is fifty digits and `Arbitrary` goes to as many as a caller asks for, which is what
   `docs/adr/0011` decides. Until the grid fixes of 2026-09-04 the evidence was weaker still, since
   the points lay on a line and `pi` was sampled like a variable.

   What has **not** changed is the shape of the objection. Fifty digits makes the unsettled bucket
   an honest one rather than a hopeful one; it does not make the fragment wider, and a transcendental
   identity that agrees to fifty digits is still a lead for a person rather than a theorem.
3. **Conjecture supply is not the scarce input.** Several thousand machine-readable open
   conjectures sit in public repositories, most untouched. The scarce inputs are verification and
   the capacity to read what comes out.

The half that is right, and worth acting on: refutation. A numeric witness where an identity was
expected is true, immediate, and carries no novelty question. And `Discovery.disagreement`
evaluates through the algebra system's own `eval`, so the refutation arm already works on the
whole language while only certification is fragment-bound. That asymmetry is the most useful
structural fact about this codebase, and it is why the Collatz harness is the highest-value week
available.

**And on 2026-09-13 something finally made the two arms disagree, which is the observation that
says the asymmetry is real rather than stipulated.** The proposal buckets exist to separate a
claim that no PROCEDURE can settle from a claim the MODEL refutes at a point, and those are
different facts about a claim rather than two strengths of one. The trouble with the separation
is that until that day nothing had exercised it. Every recent addition to the library named a
constant the model does not interpret -- the floor and the ceiling, the factorial, the absolute
value and the three beside it -- so the claims derived from them were unsettled by the procedures
AND unrefuted by the model, and the bucket that counts what a claim mentions grew while the
bucket that counts what is refuted at a point stood still. The two arms were only ever shown
apart by claims neither of them could touch, which demonstrates nothing: a pair of instruments
that both say nothing agree.

The claim that separated them was produced by the generator itself, out of a lemma about powers,
by swapping a multiplication for an addition:

    Power (x + y) z = Power x z + Power y z

It is FALSE, and each arm reaches that differently or not at all. `Ring` normalises to a sum of
monomials over ATOMS, and an atom is a term the procedure has decided not to look inside; a power
at a VARIABLE exponent is one, since nothing there expands it. So the two sides are two DISTINCT
atoms that no ring identity relates, there is nothing in the claim for a decision procedure to
work on, and it comes back unsettled. (Not, as an earlier draft of this paragraph had it, because
the ordering compares head constants by name: that decides where an atom sits inside a monomial
and says nothing about whether two atoms are related. The conclusion was right and the mechanism
under it was not, which is the failure this document spends several sections on.) The model evaluates the same sentence at `x = y = 1` and `z = 2` and
gets four against two. So the claim sits in the unsettled bucket and in the refuted-at-a-point
bucket at once, which is what the pair was built to make visible and had not made visible before.

The counts are pinned where they are measured, in `ProposeSpec`, and are deliberately not
repeated here: a number the code computes belongs in one place, and this repository has spent an
afternoon on what happens when it lives in several. What belongs here is the structure, which
does not move when a lemma lands.

Two smaller things worth recording beside it. The mechanism is the same one that made the lemma
worth adding in the first place -- a downstream development was paying a full induction for every
pair of bases because `Ring` cannot relate two powers at a variable exponent -- so the generator
rediscovered the boundary of the fragment by walking into it. And the statement it produced is
the same one the library's own test file carries by hand as that lemma's false control, written
hours earlier by a person choosing the likeliest error. A generator swapping an operator and a
writer picking a plausible mistake arrived at one sentence, which is the only evidence here that
the two notions of a plausible mutation coincide at all.

What would change the verdict on generation: a fragment with no decision procedure, which means
`exp`, `log`, trigonometry and limits, which means the type-definition rule, the naturals, and
functions defined rather than assumed. Months, in the order below.

### What the decision procedures did to that verdict, and the answer about the generator

The three reasons above were written when RING decided polynomial identities and LINARITH decided
the goals that happen to be a plain sum of their hypotheses. On 2026-09-05 LINARITH became a
decision procedure for the linear fragment, the non-strict order and equality hypotheses included,
and the model search began deciding a linear premise set exactly instead of sampling it.

That makes the first reason **stronger**, not weaker. The region where a candidate can be certified
grew, and it is precisely the region where certification carries no information, because anything
in it was computable before the candidate was proposed. A generator pointed at it would produce
entries whose verdicts were never in doubt.

So the generator is not built, and this is an answer rather than a deferral. What was built instead
is the other half of the same loop, which is the half this document has said twice the return is
in:

- a set of premises is decided rather than sampled, so "are these measurements consistent" has an
  answer where it used to have a refusal;
- an entailment that fails comes back with the point that refutes it, exactly, which is what the
  missing premise has to exclude;
- a proof says which of its premises it rests on and with what weight, so the upper bound a sequent
  carries becomes the exact support. That answers, for the linear fragment, the limit the standing
  analysis names first about using hypotheses as a domain model;
- and, since 2026-09-10, an entailment that fails comes back with **what would have to be assumed**
  for it to hold. `Abduce` proposes a bound on a linear form the goal already writes, proves the
  goal with it before reporting it, and keeps three answers apart: the premises that close the goal,
  the ones that close it by making the premise set impossible, and the ones that close it without
  the premises taking any part. The last two are each a premise doing the opposite of what an author
  wants, and each was reported as an answer by a version of this: the impossible one by the
  prototype, and the circular one by the first version that shipped.

  **Since 2026-09-11 the threshold is solved for rather than guessed**, which is the difference
  between proposing candidates and solving for the missing premise. The region where the premises
  hold and the conclusion fails is a polyhedron, and the weakest bound of a given shape on a given
  form sits at the supremum of that form on it, which the simplex in `Farkas` computes exactly.
  Measured the day before: five of six goals were offered something strictly stronger than
  necessary, and one of them by an unbounded amount, because the threshold was two thirds and the
  candidates were bounds at the numerals the goal happened to write. Mathlib has no counterpart to
  this either: `linear_combination` asks the author for the coefficients.

**And the generator that was built anyway, and what the argument above survives.** `Propose` landed
on 2026-09-11 and `Sweep` joined it to the ledger the same day, so this section's claim can now be
checked instead of argued. One pass over this repository's own library, on that date: 115 proposals
of which 20 were a claim the pass had already asked about, 95 distinct claims put to the whole
tactic surface, and the verdicts were 28 proved, 34 open, 28 disproved and 5 outside the theory.

**The 28 proofs are what the paragraph above predicts.** Every proposal is a lemma the library
already holds with a hypothesis dropped or an operator swapped, so a proof of one is a proof inside
the region the procedures decide, and nothing in it was in doubt before the candidate existed. One
of the 28 is the shape that would have been a finding — a lemma proved without a hypothesis it
states — and it is not one: `Field` proves `!x. x * inv x = 1` while assuming exactly the `~(x = 0)`
that was dropped, so the hypothesis moved from the left of the arrow to the left of the turnstile
and went nowhere. `Propose.Finding.unnecessary` reads the report rather than the standing for that
reason, and the audit over the whole library reports **no** over-stated lemma.

What the pass is for is the other 34, and the honest description of them is *claims no procedure
here settled*, which is a description of the machine and not of mathematics. The figure worth having
is per source and it differs between them — 0.42 open per settled for dropping a hypothesis against
0.31 for substituting an operator — and that answers **where a person's attention goes per unit of
machine time**, which is a question about an afternoon. It is not evidence that anything was
discovered, and nothing in the pass answers the objection above. What it removes is the older
excuse: the loop is now measured rather than reasoned about, and the measurement agrees with the
argument.

**And the measurement that says whether any of this works, which did not exist until 2026-09-12.**
The card that asked for a generator puts one thing before every source: does the loop find the
lemmas we already have? If it does not find those it will not find the others, and every sentence
above is anecdote without it. The figure now exists and is asserted in `RediscoverySpec`.

Of the library's 233 entries, **55** write one of the four operators the substitution source swaps,
outside a lambda, which is what it needs in order to produce anything at all. The loop reproduces
**12** of those 55 from a *different* lemma, by 16 distinct mutations, and proves every one. The
pairs are the ring's two commutative-monoid symmetries and the order's strict and non-strict
families: `ADD_SYM` with `+` swapped for `*` is `MUL_SYM`, and a reader can check that sentence
without running anything, which is the point of naming them rather than counting them.

The measurement is leave-one-out rather than the halved library the card describes, and it costs one
pass instead of two. Every mutation is a function of one source lemma, so asking of each proposal
whether it states some lemma **other** than the one it came from is the leave-one-out question asked
of all 233 at once. A halved library would also make the answer depend on where the split falls:
`ADD_SYM` and `MUL_SYM` in the same half makes that rediscovery unobservable, and no split avoids
every such pair.

**Zero of the 117 weakenings rediscover anything**, which is the confirmation of an argument this
repository had been making in prose: dropping a hypothesis makes a lemma weaker, and a weaker form
of something already held is not a lemma anybody was missing. It also names the ceiling on all of
the above: the loop has exactly **one** source that can rediscover, so every figure here is a figure
about four operator swaps.

The price splits the twelve in two, and that split is the part worth reading. Four are settled by
the ring normalisation at once, at 77 and 108 inferences. The other twelve are order facts the ring
does not decide, at 3706 to 7351: forty to seventy times more for a claim of exactly the same
standing. The novelty scale calls all sixteen not-news either way, which is it working on its own
hardest case, since a rediscovery is precisely a claim that looks new and is not.

**The fourth source, which is the one with the architecture this document argues for.** `Family`
landed on 2026-09-11 and it is the one place where the proposal is arithmetic on numbers and the
check is a theorem: it computes a finite sum's first ten values, fits the polynomial through them by
finite differences, states that they agree at every `n`, and puts that to `Induct`. Faulhaber's
first four come back certified without anybody having told it the answer — `Sum (\i. i^3)` is a
quartic found from the values 0, 0, 1, 9, 36, 100 and proved in 37859 inferences.

That is **not** the same activity as pointing a generator at a decidable region, and the difference
is the reason this one was built. The fragment it works in has no decision procedure: `Induct`
proves or refuses, and a claim about every natural number is not something `Ring` can settle. So a
certified answer here carries information that the answer for a ring identity does not.

What makes the claim statable at all is `real_of_num`. `num` has no arithmetic a polynomial could be
written in, and the embedding turns the induction step into a ring identity in one atom, which is
the whole of why the naturals landing made this source reachable.

Its own limits are stated where it lives: only sums, only polynomial closed forms, and a fit that
agreed at every sampled point and did not hold comes back carrying the claim rather than being
called a discovery.

**The first source landed on 2026-09-13, and it is the only one whose proposal is not a rearrangement
of something already held.** `Algebraic` puts the powers of a sum of radicals to the lattice reduction
`Relation` has carried since 2026-09-11 and turns what comes back into a theorem. `sqrt2 + sqrt3 +
sqrt5` gives `x^8 - 40x^6 + 352x^4 - 960x^2 + 576`, certified in 111048 inferences; `cbrt2 + cbrt3`
gives `x^9 - 15x^6 - 87x^3 - 125`. Nobody told it either answer, and neither polynomial is in the
library or derivable from it by any rearrangement of a lemma that is.

Both of those are sums of roots of a single degree, and every polynomial such a sum produces has
zero odd coefficients, which is a fact about the symmetry rather than about the search. The
coverage report found the consequence before anybody noticed the cause: the spelling of a
degree-one term had never been executed by anything this source produced. `sqrt2 + cbrt2` breaks
the symmetry and gives `x^6 - 6x^4 - 4x^3 + 12x^2 - 24x - 4`, whose odd coefficients the search
found rather than a test constructing them. That one is also checkable from outside this
repository, being the known minimal polynomial of that value, and it was recomputed independently
from the six conjugates before the row asserting it was written.

Two things about it are worth stating, because they are the parts a reader should not take on trust.

The **claim is provable without anything new**, and that is why this source exists now rather than
after the reals are constructed. What the card called the blocker was digits; the note under it on
2026-09-11 found the larger half, which is that a relation among real *constants* cannot be stated
here at all. A relation among algebraic values can: the claim is about any reals whose squares are
2, 3 and 5, which is an implication between polynomial equations. `Ring` cannot decide it, so the
untrusted side reduces the polynomial modulo the defining equations and hands over the cofactors as
a certificate — and a wrong certificate is a false ring equation, refused.

The **theorem is narrower than the search**, and the two are not merged. The degree is walked upward
and the first credible relation is taken, so the degree is evidence of minimality; the theorem says
only that the polynomial annihilates every such sum. And a numerically correct answer can still fail
to be a theorem: `sqrt2 + sqrt8` satisfies `x^2 - 18` with digits to spare, while the claim over
every pair whose squares are 2 and 8 is false at `(sqrt2, -2 sqrt2)`, and the reduction says so
rather than the kernel. That row is this document's own argument run as an experiment instead of
asserted.

**The third source is declined, and that is a measurement rather than a preference.** Mining the
algebra system means running the normalisers over a population of generated expressions and
proposing every pair that normalises equal. Four hundred random expressions over `+`, `-`, `*` and
small powers give 905 such pairs, and every one of the first 120 put to the novelty scale comes back
`Immediate`: settled at once by the ring normalisation. It could not come back anything else, since
the pair was **selected** because the normaliser agreed and the normaliser decides that fragment.
This is the argument above with a number on it.

**And the one component of the novelty scale that was proposed and is not there.** The card asked
for three signals and called the third the strongest: whether a claim's proof needed a lemma no
previous theorem had touched. Measured on 2026-09-11 over this repository's own library, of 104
named lemmas 30 are rested on by no other held theorem and 59 by two or more, so from that side the
signal looks discriminating. The other side kills it: a certified proof here rests on eleven to
twenty-six held lemmas and they are the common infrastructure — `NUM_REP_0` is rested on by 57 of
the 104 — and put to the 37 certified proposals the generator makes, the signal fired **once**, on a
proposal resting on the lemma it was made from. It is not a bad idea; it needs a library large
enough and loose enough that a proof can reach a corner of it, and this one is not. `NoveltySpec`
pins the shape rather than the counts, so the day that changes somebody is told.

None of those produces a new theorem, and all four answer a question somebody actually asks about
an argument they wrote. The fourth is the one the conjecture card calls most valuable, and it is
worth being exact about why it is not the thing this section argues against: it proposes no theorem
for the kernel to bless. What it proposes is a premise, and what it reports is that the goal follows
from it — which is a fact about an argument that already existed.

**What changed on 2026-09-13, stated against that sentence rather than beside it.** "None of those
produces a new theorem" was written when the sources were the second, third and fourth. The first
does produce one: the degree-eight polynomial above is a statement this repository did not hold, that
no rearrangement of a lemma it holds would reach, and that the kernel signed. It is still not a
discovery in the sense the word carries in a paper — the minimal polynomial of a sum of square roots
is classical mathematics and the method is forty years old — and the claim being made is the narrow
one: the loop, end to end, now proposes something nobody supplied and gets it certified, which is
what the section asked for evidence of and did not have.

## The order to build in

1. **The kernel hole**, closed on 2026-09-03: every entry point refuses an open term, and the
   attack is a test. Done. Everything below is conditional on it staying done.
2. **The Collatz falsification harness**, as a build-failing test. Done on 2026-09-04: the grid
   is fixed and `CollatzSeriesSpec` checks every form against exact iteration, which is what
   caught the binomial series. The residue-class screen for a **new** candidate landed on
   2026-09-10 as `CollatzScreen`, which is the refutation arm pointed at the integers: it is the
   half of the loop that works on the whole language rather than on the fragment `Translate` reads,
   so a cosine sum is screened where it could not be certified.

   Two things about it are worth carrying. The points are two representatives of every residue
   class mod `2^k` rather than a range, because the `k`-th iterate depends on `n` only through
   `n mod 2^k`, so a range tests the low classes many times and the rest not at all; and two per
   class rather than one because the true iterate is affine in `n` within a class, and one point
   would be satisfied by a candidate with the wrong slope, which is the error a plausible formula
   makes. A test builds exactly that candidate and pins that one point per class would have passed
   it.

   And it refuses by name past `2^53`, where a double stops holding consecutive integers apart: a
   comparison there would report the rounding rather than the formula. Removing that bound needs an
   exact evaluator, and `Expr.eval` over doubles is the only one this repository has.
3. **Two diagnostics.** Done on 2026-09-04. A rewriter that stopped at its step limit is now told
   apart from an identity that is false: `Rewrite.atFixedPoint` asks the conversion whether it has
   anything left to do, and `proveWith` answers `NotNormalised` rather than `NotOfForm` when it
   has. And `Discovery.Unsettled` carries which of its four cases it is: outside the fragment,
   beyond the numeral budget, rewriter out of steps, and agrees everywhere but unproved. Only the
   fourth is a lead.

   Two things measured while doing it, both worth keeping. The step limit does **not** protect
   against a large coefficient: it counts passes and a pass does more work as the term grows, so
   `200 * x = 200 * x` certifies in 32 seconds and `500 * x = 500 * x` had not returned after two
   hundred. That is what `Oracle.NumeralBudget` is for, and `Discovery` consults it before
   attempting rather than after hanging. And no input was found that exhausts the standard
   normalisation at all: reversed sums up to thirty-two terms and two hundred and fifty nested
   cancellations all certify, so the third case is reachable through `Rewrite` with a rule set of
   one's own and not, so far, through the tactic.
4. **Tracks O and P.** Done, one each. Track O landed on 2026-09-04 as `OracleCertificationSpec`,
   which is the first honest number about the bridge: generated expressions paired with the algebra
   system's own answer, bucketed certified, outside the fragment, and inside it and unproved, with
   the third bucket asserted empty and a guard beside it so that an empty bucket cannot come from a
   reader that read nothing. Track P closed on 2026-09-07, when `NotationRoundTripSpec` put the
   arithmetic notation under the round-trip generator. That is the notation every axiom string is
   read through, and neither of the two properties that already ran `parse(show(t)) == t` reached
   it: `RulesPropertySpec` has the connectives and `NumeralSpec` the numerals.

   It was closed against a generator and **reopened on 2026-09-12 against the repository's own
   output**, which is the more useful population and was failing: fourteen of the 186 statements in
   `docs/lemmas.md` did not read back, all fourteen for one reason, and no generator here produces
   the shape. The track is closed again with the document in the property rather than beside it.
5. **Rational coefficients in RING.** Done, in two halves. The whole-coefficient half landed on
   2026-09-04 and removed the coefficient frontier: `1000 * x` was out of reach and is six
   milliseconds, `(x + 1)^12` is 143 ms where degree six was the ceiling, and the one Mathlib goal
   in track R that was beyond the numeral bound is certified. `Ring.expanding` keeps the old form
   for measuring against and `RingCostSpec` asserts both.

   The rational half landed on 2026-09-09, and its obstacle was not where this document had said
   it was. It needs `~(d = 0)` for a numeral denominator, that needs the order axioms, and the
   order was built on top of the ring: the requirement and its supplier were on opposite sides of
   the chain. `Positivity` is the cut, below the ring, and it proves `~(n = 0)` outright rather
   than assuming it, so nothing RING returns carries a hypothesis. That covers a numeral
   denominator and nothing else, and what covers the rest is `Coefficient.inverseOfUnit`,
   `!x y. x * y = 1 ==> inv x = y`: a term that multiplies to one cannot be zero, so the side
   condition is discharged by the arithmetic rather than by the order, and `inv (-1)` and
   `inv (2 * inv 3)` stop being atoms. `Coefficient` is the arithmetic above `Positivity`, and the
   lemmas that carry their side condition as an equation rather than as `~(d = 0)` are the
   `conditional` map its construction builds; everything left over is `Arithmetic.multiply` between
   numerals. The first design of it needed a cancellation rule and, with it, that a field has no
   zero divisors; the one that shipped needs neither, because every step multiplies by a disguised
   `1` and rearranges instead of cancelling. `inverseOfUnit` is what allows that: a factor of one
   is an inverse, and saying so asks nothing about zero divisors. Track F is where the same lemma
   is measured from the other side.
6. **A certificate search in LINARITH.** Done on 2026-09-05, and it was the second place a model
   was turned loose with the suite as the whole control. The theorems came first: `0 < 1`
   (2026-09-04), `0 < n` for every numeral, and the cancellation of a positive factor, which takes
   a cleared denominator back off without ever writing `inv`, since it is proved by trichotomy
   rather than by dividing. Then the search became a linear program, and the procedure decides the
   strict conjunctive fragment rather than the goals that happen to be a plain sum. All derived,
   never asserted, and the source scan is the control. What is left of it is the non-strict order
   and equality hypotheses, which is what a corpus of measurements is made of.
7. **The type-definition rule.** Done on 2026-09-10 as `Kernel.defineType`, transcribed by hand
   from HOL Light's `new_basic_type_definition` against Harrison's account and bundled with
   nothing. `docs/adr/0006` is the record. It cost no axiom, and 107 lines of the trusted base
   where this item forecast forty: that was measured after the fact, and `docs/proving.md` records
   it beside the rule. The naturals, induction, the recursion theorem and finite sums followed the
   same day, so what a Collatz statement still wants is an integer index, a binomial coefficient
   and a cosine rather than a type to write them over, and the discovery loop still screens where a
   decision procedure already decides: the fragment with none waits on functions defined rather
   than assumed.

   **The authorship constraint was waived, and the debt is reduced rather than closed.** This item
   asked that a model be a second reader of the diff and the author of adversarial cases and not
   the author of the rule; a model wrote it. The second reading was done later the same day by a
   session of the same model, which is not the reading the constraint asks for, and it found one
   thing: the rule did not check that the witness was a theorem of the theory it was extending, so
   a predicate naming a constant that theory does not declare defined a type whose characterising
   theorem the same theory then refused.

   **No person has read this rule against Harrison, and on 2026-09-16 that was accepted rather than
   paid.** Angelo decided the tests and the adversarial passes were enough and closed the card. The
   sentence above is the current state and not a description of a queue: what changed is that it
   stopped being work somebody owes, and what did not change is the exposure, which this document's
   own table now carries as its own row. `docs/adr/0006` has what the decision rests on, which is four
   readings and no reader, and what it deliberately does not cover, which is the other ten rules in
   the same file.

8. **The hypothesis ledger, before any generator.** Done on 2026-09-04. The loop screened,
   certified and forgot: run it twice and it did the same work twice, and the unsettled bucket it
   calls the output worth attention lived until the process exited. `Ledger` is a file of one line
   per question, with the verdict and what the verdict rested on, and each verdict answers whether
   asking again could give a different answer and after what change. A second run of a candidate
   costs a lookup.

   It does not answer the objection below, and is not meant to. What it changes is that the output
   of such a run is legible and does not repeat itself, which is a precondition for the arrangement
   being worth anything rather than an argument that it is.

Deliberately not on the list: pointing a model at `Discovery.identities`. It needs no new code,
which is why it is tempting, and it is the one arrangement that increases traffic through the two
branches the kernel does not guard while being unable to produce a new theorem on the branch it
does.

## A finding about the Collatz series, and its repair

Until 2026-09-04 `CollatzSeries.collatzK` in the algebra module implemented a binomial series
meant to give the `k`-th Collatz iterate in closed form. It failed its own base case: at `k = 0`
it should return `n`, and it returned `n - ((2n + 1)/4) * (-1)^n`, which is 1.75 at `n = 1`. No
change of sign repairs that: the single term at `k = 0` carries a cosine of the parity of `n`,
and `T^0(n) = n` carries none. Against exact integer iteration it matched neither the `3n + 1`
map nor the `(3n + 1)/2` shortcut at any small point. The grouping of the `2^k` parity paths by
their number of odd steps is what is wrong: it assumes the parity at a step is independent of the
steps before it.

The repair did not come from fitting. The Collatz repository already holds the derivation, with
the same three forms verified in exact arithmetic: the closed form `T^k(n) = (3^s n + c) / 2^k`
once the parity sequence is fixed, the cosine sum over all `2^k` paths with parity projectors as
weights, and the one-step identity `T(x) = x + 1/4 - ((2x + 1)/4) cos(pi x)`. `CollatzSeries`
now implements those, and `CollatzSeriesSpec` checks each against direct iteration: exhaustively
for small inputs, on 256-bit starts over hundreds of steps for the closed form, and through the
algebra system's own `eval` for the symbolic form before and after simplification. The `2^k`
size of the cosine form is a floor, not an inefficiency: the flat cosine expansion has full
spectral support, so no formula "valid for every `n` at once" can be smaller.
