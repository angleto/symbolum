# 0037. The rewriter bounds the term and not only the steps

- **Status:** accepted
- **Date:** 2026-09-22

## Context

`Rewrite.repeatConv` has a ceiling on **steps**, `Rewrite.DefaultLimit = 200`, and had none on the
**size** of the term it carries. A step can multiply that size, so the memory goes before the
counter arrives. Three incidents, all the same shape, none of them anywhere near two hundred steps:

| when | rule | how it ended |
|---|---|---|
| 2026-09-12 | `NUM_DIV_MOD` written backwards, left side a variable | the suite killed after **an hour**, found with a thread dump |
| 2026-09-12 | `MAT2_SURJECTIVE` / `PAIR_SURJECTIVE` | `DocumentationSpec` never finished, one thread at **540 s** of processor inside `Rewrite` on a single claim |
| 2026-09-18 | a closed rule whose right side contains its left | **heap exhausted in four and a half minutes** |

Each was repaired with a guard on a **shape**, in `Rewrite.Rule.of` and `Rule.iterable`: a left
side that is no more than one of the rule's own variables, and a closed rule that puts its own left
side back. Both refusals are exact and neither is being reconsidered here. What they cannot reach
is written in `Rule.reproduces`'s own docstring: whether an application grows the term depends on
what the matcher put in the variables, so no property of a rule with variables in it answers the
question, and nothing looks at pairs of rules at all. The next shape is a fourth guard and the list
of guards does not terminate.

## The measurement, which is what the number rests on

A ceiling has to be above every term this corpus legitimately carries, and a ceiling below that
does not fail loudly: it turns proofs that work into rewrites truncated in silence, which is the
class of defect `Rewrite.stepConv` and `Rewrite.finished` exist to make visible.

So it was measured before it was chosen. `repeatConv` was instrumented in a checkout of its own to
record, per invocation, the node count of the widest term that invocation carried, and the whole
suite was run. **2026-09-22, one whole-suite run, 44174 invocations:**

| widest term carried | invocations | cumulative |
|---|---|---|
| 1 to 31 | 25 596 | 57.94% |
| 32 to 255 | 5 214 | 98.66% |
| 256 to 1023 | 262 | 99.95% |
| 1024 to 2047 | 20 | 99.9955% |
| 2048 to 4095 | 1 | 99.9977% |
| 4096 to 8191 | 1 | 100% |

**The widest term anything in this repository carries is 7709 nodes.** It is carried by
`Induct.afterRewriting`, from a goal of 77 nodes, which is a ratio of a hundred. The next widest is
3317, in `Algebraic.derive`, and that one starts at 3317: it does not grow at all.

That maximum is declared once, as `Rewrite.WidestMeasured`, and this sentence is the one place it
is also written out. It was written out in four on the day this record landed — here, both
docstrings, and `RewriteSpec` — with nothing comparing any two of them, which was measured by
putting a different number in this sentence and watching the three document gates stay green over
64 tests. The two docstrings cite the name now. This one cannot, being a document, so `RewriteSpec`
spells the sentence from the constant and fails naming this file when they disagree: the figure has
one declaration and one guarded copy rather than four unguarded ones.

The growth ratio was measured beside it and is what rules out the other shape of ceiling. 92.6% of
invocations never grow the term and 99.99% stay under 64 times their input — but the one that
exceeds that is the legitimate maximum above, at a hundred. A ceiling on the ratio would therefore
have to sit above 128 to admit the work this repository already does, where the ceiling on the
absolute size has the whole corpus below 8192 and nothing between 8192 and the heap.

## Decision

**`repeatConv` takes a ceiling on the node count of the term, `Rewrite.DefaultCeiling = 65536`, and
reports which of three things stopped it.**

The number is eight and a half times the measured maximum and three doublings above it. What
decided it, written down so that the next person to move it moves it for a reason:

- it is above every term this corpus carries, with room for the corpus to grow by a factor;
- a rule set that multiplies the term reaches it from that maximum in three passes, so every
  incident above is stopped at once;
- a term of that width is a few megabytes, so it cannot exhaust the gigabyte heap every coverage
  floor in `build.sbt` was measured at, and the number is bounded from above by measurement rather
  than by that argument alone: `tools/verify/perturb-the-rewriters-ceiling.sh` raises it
  sixty-four times, to 4194304 nodes, and the run dies with `OutOfMemoryError` before any
  assertion can be reached.

**Behaviour is unchanged for every existing caller.** `repeatConv` already returns the theorem it
had built when the step limit ran out, on the argument that a partial normalisation is a correct
equation, and `RewriteSpec` holds a census of every call site with what it does about one. The
ceiling stops the repetition the same way. The theorem handed back is the one built **before** the
pass that crossed, so what a caller receives is never wider than the ceiling.

**What is new is the reason.** `Rewrite.Stop` is `Settled`, `Steps` or `Size(nodes)`, and
`Rewrite.repeatReporting` and `Rewrite.rewriteReporting` hand it over beside the theorem, out of
the run that was happening anyway. `Rewrite.finished` still answers the first against the other two
and still costs a pass; this answers all three and costs nothing.

**`GrewPastCeiling` is its own refusal**, and that is the half that makes the ceiling worth having
rather than merely safe. `NotNormalised` reaches `Remedy` as `RaiseALimit`, which is correct advice
for a rewriting that ran out of steps and is the exact opposite of what a rule set that multiplies
the term needs: raising the limit lengthens the run that was already going to die. The new refusal
reaches `Remedy` as `ReportADefect` naming the rule set. `Induct.afterRewriting` is the first
caller to spend it, which is also where the widest rewriting in the repository happens.

## What it costs, measured rather than argued

The width is read at every step, so every repetition now walks its term once more than it did.
`depthConv` already visits every node of the term on each pass, so the addition is a constant
factor on something already linear — which is an argument, and the argument is not the measurement.

`theories/test` on one machine, warm runs only, the same tree at the revision before this change
and at this one:

| | wall clock |
|---|---|
| before, `c0f57978` | 37.30 s, 34.71 s |
| after, with the ceiling | 32.75 s, 34.08 s, 34.43 s |

The spread inside each configuration is larger than the difference between them, and the second
configuration also runs one test that deliberately drives a rule set to 65536 nodes. **No cost is
visible above the run-to-run variation**, and that is the whole of what these five runs establish:
they do not establish that the cost is zero.

The other half of that measurement was an accident and is worth keeping. With the width check
short-circuited but the new tests left in, the same suite took **218 s and 222 s**: the doubling
rule then runs to the step limit of two hundred passes on a term that doubles every pass. That is
the ceiling's value in seconds, on this suite, against one rule.

## Consequences

A rule set that multiplies the term now stops, says so, and names the width it reached. That is the
diagnosis three incidents cost an hour, nine minutes of processor and a heap to obtain by hand.

**What the ceiling bounds is passes, not the peak of one pass.** `depthConv` applies the rules at
every node of the term, so a single pass can multiply the size by a factor, and there is no point
inside a pass where a ceiling could intervene without being part of it. The width is read on the
result of a pass. That is enough for what this is for: all three incidents needed tens of passes to
reach the heap and are stopped at the first one that crosses. It is **not** a bound on the memory
any one pass can ask for, and a rule set that explodes within a single pass is not covered by this
and is not covered by anything else either.

**The number is this corpus's and carries a date.** `RewriteSpec` asserts the relation it was
chosen by rather than the number alone: at least eight times the measured maximum and at most
sixteen. A corpus that grows past it fails loudly, as `GrewPastCeiling`, naming the width — which
is what makes being wrong about the number cheap, and is why the reporting channel is not a
convenience beside the decision but part of it.

**The three shape guards stay.** They answer a different question and they answer it better where
they apply: a closed rule that contains its own left side cannot terminate under any driver that
iterates, which is a theorem about the rule, and the refusal names the rule to the caller. Under
the ceiling alone the incident of 2026-09-18 would have become a truncated rewrite instead of an
exhausted heap, which is better and still does not tell anybody the rule was wrong.

## Alternatives rejected

**A ceiling on the growth ratio, `widest / input`.** Scale-free, and it would let a legitimately
large input stay legal where an absolute number has to be picked for the largest thing anybody
writes. Rejected on the measurement: the one invocation in this corpus with the widest term is also
the one with the highest ratio, a hundred, so the ratio ceiling would have to be set above 128 to
admit it and would then be looser than the absolute one for every other invocation. It also asks a
reader to hold two numbers instead of one.

**A fourth shape guard, on rules that grow.** This is what the card that asked for the work
predicted and it does not survive its own argument. `Rule.of` sees one rule at a time, and the two
classes left over are exactly the ones a single rule cannot decide: a rule with variables, where
growth depends on the match, and a set that reproduces collectively where no member does. A guard
on size at `Rule.of` would also refuse every definition unfolded as a rule, `MAT_MUL` at 91 nodes
against 1 being the largest here.

**Raising `DefaultLimit` or lowering it.** Two hundred is a count of how many times a rule set has
to run and says nothing about how large a term may legitimately be. They are two measurements and
only one of them existed.
