# 0054. A FRACTRAN step is a fold into `bool`, and a run is `REACH`

- **Status:** accepted
- **Date:** 2026-09-26

## Context

FRACTRAN is Conway's language whose program is a finite list of fractions and whose state is one
natural number: from `n`, multiply by the first fraction `p/q` in the list for which `n * p/q` is a
natural number, and stop when there is none (J. H. Conway, "FRACTRAN: a simple universal
programming language for arithmetic", in *Open Problems in Communication and Computation*,
Springer 1987, pp. 4-26). An interpreter of it already exists outside this repository,
`github.com/angleto/Fractran`, 70 lines of logic in Scala 2.13. What it cannot do is say anything
**about** a program. This repository can, and the question this record answers is how the language
is stated so that the kernel can check a claim about a run.

Mycelium card `f1c1bb41` asked for it. Two cards stand behind it and are not this record: `626ad37f`,
the valuation at a prime and the reading of a program as a register machine, and `b0d2ada9`, whether
Conway's result on generalised Collatz maps connects to `Collatz`.

## Decision

**A program is a `word (prod(num, num))`, read as a list, and each pair is a numerator and a
denominator.** Nothing reduces the pairs. `6/4` and `3/2` behave identically at every `n`, since
`4 | 6n` exactly when `2 | 3n` and the quotients agree, so reducing would buy nothing a step can
see. That equivalence is a claim this record makes and does not prove.

**The step is a relation, and it is defined by one fold into `bool`:**

```
FRACTRAN_STEP P n m =
  LIST_FOLD (\f r. COND (~(SND f = 0) /\ NUM_DIVIDES (SND f) (n * FST f))
                        (m = NUM_DIV (n * FST f) (SND f))
                        r)
            F P
```

The first fraction that applies decides and the rest of the list is never read, which is the "first
fraction" of the informal rule as the order of the fold rather than as an index. The empty list is
`F`, so a state no fraction applies to has no successor. That is what halting means here, and
`FRACTRAN_HALTS P n` is defined as `!m. ~FRACTRAN_STEP P n m`.

**A fraction with denominator zero never applies.** Conway's fractions are positive rationals, so
such a pair is outside the language. Excluding it inside the definition, rather than making
well-formedness a hypothesis of every result, keeps `NUM_DIV x 0`, which is chosen and says nothing,
out of every statement. A zero numerator is admitted and sends every state it applies to to `0`,
which is what multiplying by `0/q` does.

**A run is `Reaching`'s closure with the counted relation equal to the step**, so the counter is the
length:

```
FRACTRAN_REACHES P n k m = REACH (FRACTRAN_STEP P) (FRACTRAN_STEP P) n (PAIR m k)
```

No second closure is defined. `docs/adr/0043`'s recursion along a measure is not used either: a run
need not terminate, so there is no measure to recurse along.

**Runs are certified, not believed.** `Fractran.certify` takes a program and a start as numbers,
runs them in plain Scala arithmetic, and hands each step to the kernel: the product through
`Digits.multiply`, the quotient through `Value`, the test on every fraction before the one that
applies through `NUM_MOD`, which is not zero. What comes back is `|- FRACTRAN_REACHES P n k m` and,
on request, `|- FRACTRAN_HALTS P m`. The interpreter only chooses what to ask. A wrong answer from
it is a refusal from the kernel and never a theorem.

**It sits beside the chain**, like `Collatz` and `EuclidAlgorithm`. Nothing below it needs its
constants, and wiring a link moves `Chain.widest`, the reading register and the guide's map, which
is a piece of work of its own.

## Consequences

- Nothing about the axioms moves. The development defines three constants and asserts nothing, and
  what it rests on is choice, infinity and eta, which is what `Folding` rests on. `FractranSpec`
  measures that over every published fact and two certified runs, rather than this sentence
  claiming it.
- **The step is functional**, `FRACTRAN_STEP P n a /\ FRACTRAN_STEP P n b ==> a = b`, by induction
  on the program. That runs of equal length from one start end in one place follows from it by
  induction on `REACH`, and is not proved here.
- The state is a product of prime powers, which is the coding `docs/adr/0013` rejected for the
  arithmetisation of syntax, because decoding it needs exponentiation and is not Delta-0. So this
  development is **not** a route into card `89712313`'s work on the second incompleteness theorem.
  It is an object of HOL, and nothing here is stated inside the embedded theory.
- What a register machine is, and that a program is one, is card `626ad37f` and not this record.
  Until then a claim about a program is a claim about numbers: `3/2` sends `72` to `243` in three
  steps, and that it adds the exponents of `2` and `3` is not yet a sentence here.

## What was attacked, and what survived

Measured on 2026-09-26 with the development compiled against the classes of `1bcad72b`:

- **That a refusal of a wrong trace is the kernel's and not the interpreter's.** `certifyTrace`
  checks in Scala that the first applicable fraction lands where the trace says, before asking the
  kernel. With that check removed, the trace `6, 9` under `5/3, 3/2` still came back refused, by
  `Kernel.eqMp`: the theorem at hand said `10 = NUM_DIV (6 * 5) 3` and the one asked for said `9`.
  The control, `6, 10`, was certified. `tools/verify/perturb-fractran.sh` is that perturbation.
- **That a fraction skipped by the interpreter cannot be certified as skipped.** With the
  interpreter told that `5/3` does not apply at `6`, the refusal came from the remainder: there is
  no nonzero remainder of `30` by `3` to prove.
- **That the program is Conway's.** The fractions reproduce all 48 terms OEIS A007542 displays, and
  at step 8102 the state is `2^17`, where A007547 puts it. That is agreement in numbers, a check on
  the transcription and not on the kernel.
- **That reducing a fraction changes nothing**, in numbers only: PRIMEGAME with every fraction
  scaled by six produced the same 8102 states.

## Rejected

- **Adapting or depending on `angleto/Fractran`.** It would mean a cross-build between Scala 2.13 and
  3 and a publication, for 31 lines of evaluation, and `theories` would acquire a dependency that
  nothing below it has. More to the point, an interpreter believed because it is written in Scala
  is exactly what this repository does not do. The external library stays what it is.
- **A total function `FRACTRAN_NEXT` with halting as a fixed point.** It conflates halting with a
  loop: the program `1/1` sends every `n` to itself forever, and under a fixed-point reading it
  would halt at once.
- **An index of the first applicable fraction, through `WORD_NTH`.** It states "first" as "every
  earlier position fails", which is index arithmetic in every proof about a step. The fold states
  it as the order of evaluation, and `LIST_FOLD_CONS` is the one equation a step needs.
- **Well-formedness as a hypothesis.** A predicate `every denominator is positive` carried by
  every result, for a case the definition can exclude at no cost.

## Sources

Conway's paper is cited, not held: it is not in this repository and was not read for this record.
The PRIMEGAME program and its trajectory from `2` were taken from OEIS A007542, fetched on
2026-09-26, and an independent evaluation of that program reproduced all 48 terms the entry
displays, including `a(19) = 4`. `FractranSpec` certifies that step count through the kernel, and
it is the evidence the example rests on. The OEIS entry is a secondary source for the fractions.
