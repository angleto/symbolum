# 0029. The corpus asks for arithmetic and not for saturation

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`Chaining.scala` and `Prove.scala` have each written down, more than once, what the search here is
not: no given-clause loop, no saturation, no forward inference over a clause set, no active and
passive sets. `docs/evaluation.md` reports the CASC and SMT-COMP rows as zeros for that reason. A
sentence a repository repeats about itself is either a decision or a gap, and until now it was
neither: nobody had decided to build one and nobody had decided not to.

`docs/adr/0025` landed the piece that made the question answerable. A goal's own hypotheses become
facts for the duration of a question, so `H ==> C` is no longer matched whole. Its measurement, on
one command and one worktree with a single element changed between runs, is what this record is
taken with:

| configuration | the corpus pass |
|---|---|
| no route | 2 min 22 s |
| the route without `decidedUnder` | 3 min 36 s |
| the route as delivered | 4 min 47 s |

And the outcome: the showcase went from six claims settled by the surface to twelve, and **miniF2F
did not move at all** — 21 proved and 18 unsettled, before and after.

That pair is the thing to reason from. A capability that doubled what the showcase reaches moved
nothing on the corpus, which means the corpus is blocked on something else, and what that something
is decides whether a saturation loop is worth its cost.

## What the eighteen actually ask for, enumerated

Read off a `ReachSpec` run on 2026-09-18 at `cd53e89`, which prints every unsettled statement with
its name. Classified by what a prover would have to be able to do, not by what stopped it first:

| what it needs | how many | which |
|---|---|---|
| a square, and nothing else | **2**, and **both are proved since 2026-09-18**, see below | `algebra_sqineq_at2malt1`, `mathd_algebra_113` |
| substitute or solve, then evaluate | **2** | `mathd_algebra_478`, `mathd_algebra_338` |
| a system, nonlinear or with division | **6** | `amc12b_2021_p3`, `amc12b_2002_p7`, `amc12b_2002_p19`, `mathd_algebra_362`, `aime_1990_p15`, `amc12_2000_p20` |
| a genuinely hard inequality | **6** | `imo_1983_p6`, `imo_1964_p2`, `amc12_2000_p12`, `algebra_9onxpypzleqsum2onxpy`, `algebra_sqineq_unitcircatbpamblt1`, `algebra_amgm_sumasqdivbgeqsuma` |
| concrete arithmetic on naturals | **2** | `mathd_numbertheory_234`, `mathd_numbertheory_541` |

**Not one of the eighteen is a first-order search problem.** Every one of them is
`!vars. H ==> C` with no quantifier alternation to saturate over, no clause set to close under
resolution, and no Horn chain that `Chaining` and the local context do not already walk. `0025`
turned every `H` into a fact; what is left in all eighteen is deciding `C`, and in all eighteen `C`
is arithmetic.

The two easiest of them are the sharpest evidence, because their obstacle is named by the system
itself. `algebra_sqineq_at2malt1` is `x * (2 - x) <= 1`, which is `0 <= (x - 1) * (x - 1)`, and
`mathd_algebra_113` is the same shape at seven. Both are one instance of `SQUARE_NONNEG`, a lemma
this library holds. Put to the prover on 2026-09-18 they come back:

    restate it as a goal whose degree the products reach: x * x is a product ...

which is `Linarith`'s degree bound refusing, by name. A goal that one published lemma settles is
stopped by an arithmetic reach, and no amount of search over clauses moves it.

**Both were proved later on 2026-09-18, and this record is left standing rather than corrected in
place**, because what it is a record of is the measurement that chose the decision below and that
measurement was taken when it was taken. What has changed since, and what a reader of the table
above needs so that it does not mislead: `docs/adr/0032` decided the first item of the list below,
the fact pool gained a completed square, and the two goals of the first row are settled.
`ReachSpec` prints both among the statements it proves by name, so the figure is read off a run
rather than asserted here, and the eighteen are **sixteen**. The other four rows are untouched,
which was predicted in 0032 and is the half of the prediction that could have been wrong.

And the refusal quoted above is no longer the one those two would get, which is a second thing
0032 changed: a goal with no hypotheses is told its pool is empty rather than told about a degree,
since the sentence about the degree is true of an empty set and sends the reader nowhere.

## Decision

**Do not build forward inference, saturation or a given-clause loop.** The corpus this repository
measures itself against contains no goal that one would reach, and the measurement above is what
says so rather than an argument from taste.

What the corpus asks for instead, in the order the enumeration puts it:

1. **Arithmetic past the degree `Linarith` reaches**, which is Mycelium card `bacfaba5` and which
   two of the eighteen waited on alone, and which `docs/adr/0032` decided and which is built: those
   two are proved. That was the cheapest thing on this list and the only one with
   goals whose refusal already names it.
2. **Deciding a system**: producing the values a set of equations forces, and substituting them.
   Six of the eighteen, and the two "substitute or solve" ones are its easy end.
3. **Inequalities that need a certificate rather than a decision** — AM-GM, Schur, the symmetric
   ones. Six, and this is the part that is genuinely hard rather than merely absent.

`docs/evaluation.md`'s CASC and SMT-COMP rows stay zeros and their reason stays what it is. What
changes is that the absence is now decided: the row may say the loop is not there **because the
corpus does not ask for one**, and cite this record.

## Consequences

**The `Prove.searches` enumeration does not grow**, so `DocumentationSpec`'s gate on the front
page's row stays green without the row being rewritten to name a fourth search. The row gains a
citation and nothing else.

**An absence decided and an absence not faced read alike, and this is the first of the three to be
told apart.** The card this record comes from asks exactly that, and the other two — forward
inference and the active/passive split — fall with the same measurement, because they are the same
architecture read at three grains.

**Rejected: building it anyway, on the argument that the corpus is not the only consumer.** It is
the honest form of the objection and it loses on cost rather than on principle. `ReachSpec` is the
most expensive suite in this repository and `0025` already took it from 2 min 22 s to 4 min 47 s; a
loop that saturates multiplies that by whatever it is allowed, and the bound and the redundancy
criterion would be what decides whether the suite stays runnable at all. Paying that for a
population in which nothing is reached is the trade this record refuses.

**Rejected: deciding nothing and leaving the three sentences.** That is the state this record ends.
A repository that writes down four times what it is not, without ever saying whether it means to
be, is describing a gap and calling it a design.

**What would reopen this.** A corpus, or a body of work in this repository, whose goals carry
quantifier alternation or need a clause set closed under resolution. `Resolving` reasons **about**
resolution derivations and does not perform one, and `modules/sat` decides propositional
satisfiability; neither is that corpus. If the object-level work of `docs/adr/0013` reaches a point
where PA's own derivations are searched for rather than constructed by hand, that is the case, and
it supersedes this record rather than contradicting it.

**What this does not say.** It does not say a given-clause loop would be useless in general, and it
does not rank the three things the corpus asks for by difficulty — only by what the enumeration
counts. And the enumeration is of one corpus at one revision: 244 statements of which this system
can state 39, which is the population `docs/evaluation.md` argues about at length and which is not
a benchmark figure.
