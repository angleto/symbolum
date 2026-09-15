# Architecture

**EXCERPT — for anyone scanning the index:**
The correctness argument of this system, stated in full: what is trusted, why the modules depend on
each other in one direction only, what the kernel does and what it deliberately does not, and where
a change is dangerous. It is the document to read before touching `modules/kernel` or the axioms.
It does not explain how to use the system, which is [proving.md](proving.md), and it does not
re-argue the decisions, which are in [adr/](adr/).

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## The argument, in one paragraph

A theorem is a value of a class whose constructor is private to one object, and the ten inference
rules and the three theory extensions in that object are the only things that call it. Terms are
well-typed by construction, because their constructors are private to the kernel package and every
public builder checks. Therefore: everything outside `modules/kernel` may be arbitrarily wrong, and
the worst it can do is fail to produce a theorem. The computer algebra system, the rewriting engine,
the tactics, the parser and the printer are all outside. What has to be believed is the kernel, the
sixteen axioms of the theory of the reals, and, since 2026-09-10, three more: a choice operator and
eta in `modules/logic/.../Classical.scala`, and infinity in `modules/theories/.../Natural.scala`.
`docs/adr/0007` is the record of the first and the third and `docs/adr/0009` of the second, and the
first of those says why the count is going up before it comes down. A development over the reals
takes none of the three.

## The trusted base, exactly

| What | Where | Size |
|---|---|---|
| The kernel | `Kernel`, `Term`, `Type`, `Theory` | under 1200 lines, and see below for what that number does and does not say |
| Beside it, and not counted | `Printer`, `KernelError`, `Derivation`, `Proof` | display, refusals, the proof record and the writing of it out: none can build a theorem |
| The axioms of the reals | `Real.Axioms` in `modules/theories/.../Real.scala` | 16 propositions, a complete ordered field |
| The axioms about the formalism | `Classical.Axioms` in `modules/logic/.../Classical.scala` | 2 propositions, both from HOL Light's `class.ml`: choice, `SELECT_AX` with `select` for a character this lexer cannot read, and eta, `ETA_AX` over `'a` and `'b` |
| The axiom about a type nothing else interprets | `Natural.Axioms` in `modules/theories/.../Natural.scala` | infinity, in the form the naturals are carved out of rather than the one upstream asserts |

**The line count measures readability and not verification.** "Small enough that somebody could read
it" is strictly weaker than "proved correct", and the systems occupying the second niche — Candle,
verified to machine code through CakeML, and the Metamath verifiers — are available to the same
reader. How much hostile attention these lines have actually had is a different question with a
different answer, and `docs/evaluation.md` keeps the table: five passes so far, six defects in the
trusted base, and the two most recent passes found none.

That is the whole of it, and the three axiom rows are not a list kept by hand: `RealSpec` scans the
main sources for `Kernel.assertAxiom` and asserts the exact set of files that name it, which is
those three and the kernel file where the operation is defined. A fourth source of axioms cannot
appear without that assertion changing in the same commit.

**The count moved on 2026-09-10 and the file list did not**, which is the property that scan exists
for. Eta went into the file choice was already in, so what has to be believed grew while the set of
places it can grow from stayed at four; a third axiom in a third file would have failed the scan
instead of only the counts. `docs/adr/0009` records it.

No one development holds all of them, and `NaturalSpec` measures that rather than arguing it:
`Real.standard` holds the sixteen and neither of the logic's two, `Natural.standard` holds those two
and infinity and none of the sixteen, and a chain built through both holds nineteen. What
`docs/adr/0007` says about the direction of travel is that the sixteen are what the work at the end
of it turns into theorems, so the row that is largest here is the row that goes.

The two numbers are a reader's to check rather than a claim they have to accept, and
`DocumentationSpec` pins both here so that neither can go stale on its own. The first is a bound
rather than a count because what it stands for is that one person can read the whole trusted base;
an exact figure would be re-measured, and wrong, after every edit to the kernel.

Four properties hold the boundary in place, each asserted by a test rather than by this document:
- `IsolationSpec` in the kernel asserts the kernel cannot see the algebra system or the logic built
  on it. It is a compile-time assertion, because the property is that certain code does not build.
- `TrustBoundarySpec` in the logic asserts that a theorem cannot be forged and a term cannot be
  built except through the checked constructors, and `TrustBoundaryTwinSpec` in the kernel compiles
  the same lines from inside the package, so that each refusal is known to be about visibility. The
  twin holds the half a compile-time assertion cannot reach: `Thm` was an opaque type over a pair
  until 2026-09-10, and an opaque type erases to what it wraps, so a cast from the pair produced a
  theorem out of nothing while the assertion about typechecking passed the whole time. A class does
  not erase, and the twin asserts that the same cast now raises.
- `RealSpec` pins the sixteen axioms, as printed, in a copy written out in the test itself, checks
  that each is closed and mentions only declared constants, and runs the scan above, so that the
  set of files allowed to assert an axiom is asserted rather than promised. `ClassicalSpec` runs the
  same scan over the logic module alone, where the answer is one file. An axiom introduced or
  altered by accident would fail no other test: it would make more things provable, which looks
  like progress.
- `SoundnessAttackSpec` in the theories is a corpus rather than a case. Every entry names an attack,
  the defect it came from, and the refusal it must come back with **by name**, because a kernel that
  turned each one away for the wrong reason would pass a corpus recording only refused-or-taken; a
  must-accept half is there against the mirror image of that, a rule whose refusals are all correct
  and whose product is unusable. One test runs the lot and reports how many came out otherwise.
  What the corpus is not is coverage, and the file says so first: the capture hole of 2026-09-03
  survived this document, `TrustBoundarySpec`, `IsolationSpec` and the whole suite, and an
  adversarial audit rather than any use of the system is what found it.

## The module graph

```
kernel    -> (nothing)          the trusted base
checker   -> kernel             a second reading of a proof, as text or in this process
sat       -> (nothing)          a conflict-driven solver and the refutations it produces
logic     -> kernel, sat        connectives, derived rules, rewriting, parser, printer
theories  -> logic              the reals, numerals, arithmetic, RING, LINARITH
core      -> (nothing)          the computer algebra system
tactics   -> theories, core     the lowest module that sees both halves
examples  -> tactics            runnable demonstrations of either half
aggregate -> the seven above    no source: a pom, so one coordinate resolves the whole system
dist      -> tactics, examples  the tarball a person installs, and the only module that is not a
                                library and not a demonstration
```

The last two are what the system ships as, and they are two artifacts rather than one read two
ways: the six library modules go to a registry under their own coordinates for a build tool to
resolve, and the distribution carries every jar with a launcher per entry point for a person to
run.

`sat` is the second module depending on nothing, and the reason is the first one read backwards.
`kernel` depends on nothing so that what has to be believed can be pointed at; `sat` depends on
nothing so that what must **not** be believed cannot reach it. A solver that cannot see `kernel`
cannot construct a theorem, which is this document's own division enforced by the build rather than
by a reviewer, and `logic.Propositional` is the joint: it takes the refutation the solver found and
re-derives every resolution step through the rules. `mark` is in neither, for the reason it is beside the graph rather than in it: it regenerates
two files under `docs/` and is of no use to anybody who did not clone this repository. `build.sbt`
carries the argument at each of them.

The direction is the enforcement mechanism, not a tidiness preference. `kernel` declaring no
dependency is what makes an import of the algebra system from the trusted base a compile error
rather than a review finding, and `docs/adr/0003` records why a naming convention was not enough.

**The last edge moved on 2026-09-13 and the wording above moved with it.** `examples -> core` made
that directory the algebra's, so the proof half had no demonstration anywhere and the one written
that day could not be compiled there. Reading `tactics` as *the only* module seeing both halves
had been a description of the graph mistaken for the constraint: the constraint is about what is
**below** `tactics`, which is where a theorem is constructed, and `examples` is above it and
constructs none. `kernel`, `logic` and `theories` still cannot see `core`, and **what stops them is
the module graph** rather than a test: none of the three declares that dependency, so a reference to
`core` in any of them does not compile. `IsolationSpec` asserts the kernel's case on top of that, by
trying to compile a reference to the algebra system and to the logic above it, and it asserts only
the kernel's. That is not a gap to be filled by writing two more: a dependency a build file does not
declare is a stronger guarantee than a test that nothing is imported, and the spec exists because
the kernel is the one module where a reader wants the boundary asserted rather than inferred.

**Two edges are not in that picture because they exist only at test scope**, and neither reaches
anything published: the checker's tests depend on `theories`, since a checker that knows no
mathematics still needs real proofs to read, and the tactics' tests depend on the checker's, since
`docs/evaluation.md` is regenerated by one command and two of its three tables are the checker's own
counts over the proofs `ReplaySpec` replays. `build.sbt` carries the argument at each of them.

## The kernel

### What it is

Higher-order logic in the tradition of LCF and HOL: a simply typed lambda calculus with equality as
the primitive relation. Not dependent type theory, and `docs/adr/0001` says why.

Binders are not syntax. A quantifier is a constant applied to a lambda, so the single substitution
in the kernel serves every binder that will ever be defined and the trusted base does not grow when
the mathematics does.

### The ten rules, and the three extensions

```
refl            |- t = t
trans           G |- a = b,  D |- b = c        =>  G, D |- a = c
mkComb          G |- f = g,  D |- x = y        =>  G, D |- f x = g y
abs             G |- s = t,  x not free in G   =>  G |- (\x. s) = (\x. t)
beta            |- (\x. t) u = t[u/x]
assume          p |- p
eqMp            G |- p = q,  D |- p            =>  G, D |- q
deductAntisym   G |- p,  D |- q                =>  (G - q), (D - p) |- p = q
inst            replace free variables throughout
instType        replace type variables throughout
```

Plus three operations that extend a theory. `defineConstant` is conservative under the two
conditions it enforces. `defineType` is conservative too, and is the one that makes a new type
possible without an axiom: given a predicate and a theorem that something satisfies it, it declares
the type, two constants, and returns the bijection

```
defineType      |- P w   =>   |- abs (rep a) = a,  |- P r <=> rep (abs r) = r
```

transcribed by hand from HOL Light's `new_basic_type_definition`; `docs/adr/0006` records the
decision and what it turns away. And `assertAxiom`, which is not conservative and is named so that
it reads as what it is at the call site: it is the only one of the three that moves what has to be
believed.

### The term representation

Locally nameless: a bound variable is a de Bruijn index, a free variable is a name carrying its
type. Two consequences, and they are the reason for the choice:

- Alpha-equivalence is `==`. `\x. x` and `\y. y` are one value.
- Substitution cannot capture. Replacing a free variable, or instantiating a type variable, touches
  only nodes that carry names, and what goes in their place is a locally closed term. The renaming a
  name-carrying representation needs here does not exist, and neither do its mistakes. The premise
  is checked, not assumed: the extractor on an abstraction hands out a body that is not locally
  closed, and every operation that accepts a term refuses it.

`docs/adr/0002` records the alternatives and what this one gives up.

### What the kernel deliberately does not do

- **Proof terms, closed on 2026-09-10, and then closed further the same day.** A theorem records its
  derivation, and `modules/checker` reads one without touching a kernel rule. The first reading ran
  in this process and read the kernel's terms through the kernel's extractors, so a defect in
  **those** would have told it the same story they tell everyone. `Kernel.Proof` now writes a
  derivation out as text and `Parse` in the checker reads one back, naming no kernel type at all, so
  the extractors are out of the argument: `12 * 12 = 144` is 1132 steps over 2048 distinct terms in
  65 KB, and the two routes agree about which axioms it reaches. What is left shared is the
  **writer**, and nothing can remove that: something has to put the proof down, and a writer that
  puts down a proof other than the one derived produces a table that fails to check.
- **Theory lineage, narrowed on 2026-09-10 rather than closed.** A theorem still does not record
  which theory it was proved in. What it has instead is that a **defined** constant carries the term
  that defined it, so two theories that *define* one name differently give two constants that are
  different terms, and for those `|- c = T` and `|- c = F` no longer chain into `|- T = F`.
  `SoundnessAttackSpec` derived that falsity before the change and asserts the refusal after it,
  which is one test read in the other direction. `docs/adr/0008` has the decision, the alternative,
  and the two prices: two constants that differ only in origin print alike, so the refusal has to
  say why rather than report that `c` is not `c`, and a theorem about a declared constant no longer
  combines with one about a defined constant of the same name, which is a valid inference given up
  on the safe side.

  **What this does not cover, and it is the half the theory is mostly made of.**
  `Theory.declareConstant` records no origin, and `Theory.constant` reads the origin table, so a
  constant that is declared and then given its meaning by axiom carries no origin at all. `+`, `*`,
  `<`, `inv`, `0` and `1` are all of that kind: `Real.scala` introduces them without defining them
  and the sixteen axioms are what say anything about them. Two theories that axiomatise one of those
  names differently therefore produce constants that compare **equal**, and their theorems mix,
  which is the scenario this bullet used to describe in full and now describes for definitions only.
  Found by an adversarial audit on 2026-09-10 and not repaired here; a repair is a kernel change and
  is recorded rather than made in passing. **It derives, and that was measured rather than argued
  on 2026-09-12**: two theories that each declare `p : bool` and axiomatise it the opposite way give
  `|- F` with no hypotheses, and the row is in `SoundnessAttackSpec` beside the ones that are
  refused, filed as a limit rather than a must-refuse because the repair is the decision below and
  not a missing check. Reaching it takes a caller who builds two theories on purpose and then
  combines their theorems; there is one theory of the reals in ordinary use. The lineage on every theorem that would close the whole
  of it is what Isabelle carries and HOL Light does not need, having one global theory.
- **The signature invariant, which holds where belief is added and not everywhere.** *A theorem of a
  theory names only that theory's signature* is the rule `docs/adr/0006`'s second reading named and
  repaired for `defineType`. It is not true of the kernel as a whole, and the exact statement is
  this: `Theory.checkType` refuses a type operator nobody declared and `Theory.checkTerm` reaches it
  through the types of free variables and of binders, and the only rules that call either are the
  **three theory extensions**. Everything else takes the type the caller wrote.

  Three ways in, found on 2026-09-10 by an adversarial re-reading and pinned as rows in
  `SoundnessAttackSpec` rather than described here: `Kernel.instType` substitutes any `Type` at all,
  `Kernel.inst` substitutes terms carrying any type at all, and `Term.variable` is public and
  unchecked, so a type nobody declared is already inside a term before a rule is asked. The last of
  those is why giving the two rules a `Theory` would not close it.

  **Why this is a broken invariant and not a falsity.** A type operator no theory declares is
  uninterpreted, and every model of the theory extends to a model of the theory plus that operator,
  because a HOL type denotes a non-empty set and nothing in this logic can prove a type empty. A
  theorem with a type variable holds for every non-empty interpretation of that variable, so its
  instance at the new operator holds in every such extension. What could still go wrong is
  **recycling**: a statement about `ghost` becoming an axiom, or a definition, in a theory where
  `ghost` means something else or has another arity. All three extensions call `checkTerm`, so that
  door is shut, and `SoundnessAttackSpec` holds the two rows that show it shut beside the two that
  show the invariant broken.

  **Not repaired here, and the reason is that it is the same question as the bullet above.** Making
  the invariant true in general means a theorem knowing the theory it came from, which is the
  decision `docs/adr/0008` deferred for declared constants. Repairing half of it at two rules would
  cost two of the ten signatures and leave `Term.variable` open, which is a worse arrangement than
  the one written down: a guard that looks complete and is not.

- **No consistency claim.** Nothing here establishes that the axioms are consistent. The sixteen
  are standard and their consistency is a known result; choice and eta are `SELECT_AX` and `ETA_AX`
  under their own spellings, and infinity is not upstream's form but a statement `Natural.scala`
  argues holds in the same intended model. That those three files state what they mean to state is
  ours alone.

Each of these is written where it lives, on the type it concerns, rather than only here.

## The definitional discipline

Everything above the axioms is definitional, and that is what keeps the trusted base to the kernel
and the three files that assert an axiom.

| Layer | How it extends the theory | Conservative? |
|---|---|---|
| The eight connectives | `defineConstant` | Yes |
| Binary numerals `BIT0`, `BIT1` | `defineConstant` | Yes |
| Subtraction, division, `<=` | `defineConstant` | Yes |
| Every arithmetic lemma | proved from the axioms | Yes, it is a theorem |
| The excluded middle | proved from choice | Yes, it is a theorem, and `ClassicalSpec` pins the axioms it reaches |
| The sixteen axioms | `assertAxiom` | **No.** This is the non-conservative content of the theory |
| The choice axiom and eta | `assertAxiom` | **No.** The non-conservative content of the logic, and the two of them are all of it |
| The axiom of infinity | `assertAxiom` | **No.** What the naturals are carved out of |
| The type `num` | `defineType` | **Yes.** Defined, so it adds nothing to the three above it |
| The type `prod` | `defineType` | **Yes.** Carved out of `'a -> 'b -> bool`; four of its eight theorems reach no axiom at all |
| The type `word` | `defineType` | **Yes.** A length and a padded function, carved out of `prod(num, num -> 'a)` |

Declaring a constant without defining it is also conservative: an uninterpreted name proves nothing.
The axioms are what give `+`, `*` and `<` their meaning.

## Where a change is dangerous

In descending order of how much damage a mistake does:

1. **`modules/kernel/src/main`.** A bug here is unbounded: it can make the system prove anything.
   Read the whole file you are changing, not the function. The tests in `modules/kernel/src/test`
   cover each rule in the case where it applies and the case where it must refuse, and the refusals
   are the half that matters.
2. **`Real.Axioms`.** A mis-stated axiom makes everything provable, and the only test that fails
   is the pinned copy in `RealSpec`, which fails because the text changed and not because it is
   wrong. Read a changed axiom against a textbook, out loud, and change the pinned copy in the
   same commit. The same goes for a definition body in `Real.Definitions` and for the notation:
   both decide what an axiom string means, and neither is checked by anything but a reader.
   [reading-register.md](reading-register.md) is where that reading is recorded, one row per axiom,
   per defined constant and per spelling, generated from the code and pinned by `RegisterSpec`. It
   checks none of them and could not; what it does is give the reading a state, so that a statement
   enters the system unread, its absence from the list fails the build, and a rename takes its
   attestation with it.
3. **`Arithmetic.ringOrder`.** The rewriting sorts by it, and cancellation is a rewrite between
   neighbours. Changing it to the obvious structural order puts a term and its negation at opposite
   ends of a sum, where they never meet, and cancellation silently stops working. The comment there
   records the version that was wrong.
4. **The ordered rewriting rules.** `orderedRewriteConv` terminates because the rules used with it
   keep the size of the term fixed, so a total order on terms of one size is well-founded. A rule
   that grows the term needs a different argument and must not be used with it.
5. **Everything else.** A mistake costs a failed proof. That is the point of the arrangement.

## Reading order for someone new

1. This document.
2. `docs/adr/0001` and `0003`, which are the two decisions everything else follows from.
3. `modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Kernel.scala`, the whole file, which the bound
   above is there to keep to one sitting.
4. `docs/proving.md`, and then run the examples.
