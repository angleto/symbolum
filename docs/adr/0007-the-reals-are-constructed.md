# 0007. The reals are constructed, and the foundation gains the classical axioms

- **Status:** accepted, revises 0004
- **Date:** 2026-09-10

## Context

[`0004`](0004-reals-axiomatised-not-constructed.md) introduced the reals by axiom and rejected
the construction on schedule: months of work upstream of every result the project wanted, against
a risk that one small file and a drift test already bounded. That reasoning was right when it was
written and the schedule argument has not been refuted. What has changed is everything around it.

**0004 left the door open and named the property to preserve.** Its own consequences section says
that replacing the axioms with a construction later "is a change to one file's contents and to
nothing that depends on it, as long as the constructed type ends up satisfying the same
characterising theorems under the same names", and that this is why the axioms are stated as the
properties consumers use rather than as a minimal presentation. This record walks through that
door. It does not overturn 0004's argument; it takes the option 0004 designed for.

**The mechanism that was missing now exists.** [`0006`](0006-a-type-is-defined-by-a-bijection-with-a-subset.md)
put `Kernel.defineType` in the kernel on 2026-09-10. Before it, a construction was not merely
expensive, it was impossible: every type had to arrive as an axiom, so building the naturals would
have cost more axioms than assuming the reals.

**Three separate questions turned out to have one answer.** `inv 0 = 0`, which
`RingCorpusSpec` carries as the first entry on any exception list that records a difference between
two theories rather than a limit of this prover. The naturals, which are the next step of the
roadmap in `CLAUDE.md`. And Collatz, finite sums and sequences, which want the naturals, the
integers and the rationals whatever is decided about the reals. Once the rationals exist, keeping
sixteen axioms beside a real number that could be constructed from them is the position that needs
defending.

Four measurements bound the work. Each was taken on 2026-09-10 against the sources rather than
recalled:

- **The foundation is currently empty.** `Kernel.assertAxiom` is named in exactly two main
  sources, the kernel that defines it and `Real.scala`, and `RealSpec` asserts that allowlist. The
  logic module has no axioms at all: the eight connectives are definitional extensions. So what is
  believed today is ten inference rules plus sixteen statements about an ordered field, and nothing
  about the formalism itself.
- **The kernel's ten rules are HOL Light's ten**, and there is no eta rule among them or anywhere
  else in the sources. Extensionality of functions is therefore not available and would be an
  axiom, exactly as it is in HOL Light.
- **`defineType` requires a closed predicate** (`Kernel.scala`, the `DefinitionIsNotClosed`
  branch). A witness obtained by eliminating an existential is a variable, so a predicate built
  from it is not closed and cannot define a type. This is what forces a choice operator into the
  foundation: the function the axiom of infinity says exists has to be **named** before a type can
  be carved out with it, and naming a witness is what a choice operator is for. The foundation
  cannot be infinity alone.
- **A polymorphic constant needs no kernel change.** `Theory.declareConstant` takes a type schema
  whose type variables a use site may instantiate, and `Theory.constant` matches an instance
  against it, so a choice operator at `('a -> bool) -> 'a` is declarable today.

## Decision

The reals are constructed from the naturals. The foundation gains the classical axioms of
higher-order logic, asserted **one at a time, in the commit whose derivation needs one**, and never
in advance.

The order, and each step's reason for being where it is:

1. **A choice operator and its axiom.** Before the naturals rather than after, for the reason in
   the context: a type is defined by a closed predicate, so the successor function has to be named.
2. **The axiom of infinity**, on a declared type. It is asserted about a type, so there has to be a
   type to assert it about, which is why it cannot come first.
3. **The naturals**, by `defineType` over the smallest predicate containing zero and closed under
   successor, then induction, then the recursion theorem. Nothing here is asserted.
4. **The integers and the rationals** as quotients, then the reals as a completion. The sixteen
   become theorems under the same names and the same printed forms, and `Real.scala` stops
   asserting.

**Extensionality is not asserted until a derivation needs it.** It is the third of HOL Light's
three axioms and it may or may not be reached on this path. An axiom asserted in advance of the
derivation that wants it cannot be justified by pointing at that derivation, which is the only
justification an axiom in this system gets.

**The axioms live where what they are about lives.** Choice and extensionality belong to the logic,
infinity belongs with the naturals. `Logic.standard` stays axiom-free and the classical axioms
arrive in an extension beside it, so that a development can be asked which of its results need
choice; everything downstream already takes the logic it is built on as an argument. `RealSpec`'s
allowlist grows by one file per axiom, in the commit that adds it, which is what makes an accidental
growth of the trusted base fail the build rather than pass it.

**Who writes them, and who reads them.** `docs/evaluation.md` places a new or edited axiom in the
first of the four slots where nothing checks truth, and 0004 calls a mis-stated axiom the sharpest
risk in the system: it makes everything provable, every test still passes, and nothing reports a
problem. Unlike a kernel rule, an axiom is three lines rather than a hundred, so reading it against
a source is the whole of the work and is the same job whoever typed it. The arrangement is
therefore that each axiom is written with its source named in the commit message, and does not land
until a person has read the statement against that source. This record names, per axiom, who did.

## Consequences

**The count gets worse before it gets better, and stays worse for the whole construction.** Sixteen
today, eighteen or nineteen once choice and infinity land, then two or three when the sixteen become
theorems. Every session between the first step and the last sees a trusted base larger than today's.
That is a consequence of the decision and not a defect, and it is written here so that it is not
read as one.

**The risk 0004 named is increased during the transition, not reduced.** Three more asserted
statements in the slot where nothing checks truth, held for months, in exchange for removing sixteen
at the end. The arithmetic is favourable only if the last step is reached.

**The logic stops being intuitionistic.** `docs/proving.md` says that disjunction and the
existential are intuitionistic here, that `p \/ ~p` is not reachable, and that `LT_TOTAL` is where a
proof by cases gets its disjunction. Choice gives the excluded middle by Diaconescu's argument, so
those sentences change when step 1 lands, and the theory of the reals stops being the only supplier
of a case split.

**There are two logics and a caller picks.** That is a cost at every call site that constructs one,
and it is the price of keeping the classical commitments visible rather than global.

**The naturals arrive later than the alternative below would have delivered them**, and the
statements that wait on them, Collatz and finite sums among them, wait on the recursion theorem
either way.

**Nothing that consumes the reals has to change**, provided 0004's property is preserved: the
sixteen keep their names, their statements and their printed forms, and become theorems. `RealSpec`
pins the printed form of each, so a construction that arrives at a different statement fails that
test rather than passing quietly. That test changes meaning from "these are the axioms" to "these
are what the construction has to reach", which is the same list read from the other side.

**`inv 0 = 0` is deferred, not declined.** `inv` becomes a defined constant, so the convention
becomes a choice inside a definition and costs no axiom. Until step 4, `inv 0` stays unspecified,
`Ring` keeps refusing lines 65, 66 and 70 of the ring corpus, `Field` keeps proving them at the
price of one condition naming one variable, and the exception list in `RingCorpusSpec` keeps
recording a difference between two theories. What changes today is only that the entry now points
at a decision with a date instead of an open question.

## Alternatives rejected

**The naturals as the least inductive subset of the reals, now.** `NUM_REP n` is
`!S. S 0 /\ (!x. S x ==> S (x + 1)) ==> S n`, the witness `|- NUM_REP 0` is immediate, and
`defineType` does the rest. It costs **no axiom at all**, because a complete ordered field is
already infinite and the sixteen prove it; induction falls straight out of the definition; and the
embedding of the naturals into the reals arrives free as the representation function, which is the
coercion the eleven unreadable entries of the ring corpus are written with. It is strictly the
cheapest way to have the naturals in this system as it stands today.

Rejected because it is circular under this decision. The construction needs the naturals **below**
the reals, and this builds them above. The construction file would be written in order to be thrown
away, and while everything proved on top of the naturals would survive the swap if they were used
only through zero, successor, induction and the coercion, the discipline that guarantees that is
one more thing to maintain for the duration. It remains the right answer for anyone who keeps 0004,
and it is recorded here so that whoever finds it attractive later finds the reason it lost rather
than rediscovering the idea.

**Assert `inv 0 = 0` as a seventeenth axiom.** It closes three rows of the ring corpus and buys
parity of reading with Mathlib on every goal written with an inverse. Rejected because the
seventeenth statement would not be a field axiom, so the set stops being exactly a complete ordered
field and loses the property that a reader can check it against a textbook in one sitting, which is
the mitigation 0004 rests on. Worth knowing while judging that trade: Mathlib does not get it free
either. `inv_zero` is a field of the `GroupWithZero` class that `Field` descends from, so it is an
axiom there too and merely uncounted, and HOL Light proves it because HOL Light constructs. Under
this record the question dissolves instead of being answered.

**A definite description operator instead of a choice operator.** Weaker, and therefore preferable
if it sufficed: description names the unique thing satisfying a predicate. Rejected because the
witness that has to be named is not unique. The axiom of infinity says some injective and
non-surjective function exists, not which, so description has nothing to name.

**Assert all three classical axioms at once and be done.** Rejected on the rule above: an axiom
asserted before the derivation that needs it has no justification available, and extensionality may
not be needed on this path at all. Asserting it to match HOL Light's list would be matching a shape
rather than a requirement.

**Keep the axiomatised reals beside a constructed one.** Two types of real number, theorems about
each, and nothing to stop the two being mixed. It is the same failure `0006` refuses for a type name
already in the theory, one level up, and the cost is that no reader can tell which real a theorem is
about.

**Construct the reals but keep the sixteen as a characterisation, asserted.** Superficially
attractive: the construction gives the type, the axioms give the properties, and the tactics need
not change at all. Rejected because it keeps every one of the sixteen in the trusted base while
paying the full cost of the construction, which is the worst cell of the table. The sixteen become
theorems or the construction bought nothing.

## What is true today

Nothing in this record changes what the system asks anyone to believe on the day it is written.
`Real.scala` asserts sixteen axioms, `RealSpec` pins them, the allowlist holds two files, and the
foundation is still empty. What this record changes is what the system will ask, and in which
order.
