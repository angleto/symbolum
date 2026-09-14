# 0002. Locally nameless representation for binders

- **Status:** accepted
- **Date:** 2026-09-03

## Context

Decision 0001 puts every binder in the kernel's lambda, which concentrates all of the binding
machinery in one place. That place is inside the trusted base, so its representation decides
where the subtle errors can hide.

Two operations have to be exactly right: substitution must not capture a variable, and two terms
that differ only in the names of bound variables must compare equal. Both are needed by almost
every primitive rule, so a mistake in either is not contained.

The local evidence that this is worth deliberating over is in the CAS: `replaceSymbol` walks into
the body of `Integral` and `Derivative` without regard for the variable they bind, because the
representation gave nobody a reason to think about it.

## Decision

Bound variables are de Bruijn indices; free variables are names carrying their type. A term under
a binder is opened into a fresh free variable when a rule needs to look inside it, and closed
again when the rule rebuilds it.

Alpha-equivalence is therefore structural equality, and the kernel contains no renaming.

Terms are well-typed by construction, and locally closed by checking. An index with no enclosing
binder cannot be written through the public constructors, but the extractor on an abstraction
hands out its body, and that body has one. So every operation that accepts a term, in the kernel
and in `Theory`, checks that the term is locally closed and refuses it otherwise. Until it did, a
body obtained that way could be put back under a binder of another type, and `|- 0 = 1` followed;
an audit exhibited it, and the attack is now a test.

## Consequences

The two operations that most often go wrong stop being able to go wrong. Equality is `==`, and
substitution of a locally closed term for a free variable cannot capture, because a free variable
is a name and the thing being substituted has no loose indices. The kernel checks that premise at
the boundary rather than assuming it.

The cost is paid at every binder boundary: open and close are explicit, and forgetting one is a
type error only some of the time, so those two functions need direct tests rather than being
exercised incidentally.

Debugging is worse. A term printed raw shows indices, which nobody reads fluently, so the printer
becomes necessary earlier than it otherwise would be, and error messages from the kernel have to
go through it.

The bound name a caller wrote is not kept anywhere. `Term.Abs` holds a type and a body, so a claim
read from somebody's text and printed back comes back under names the printer invented:
`!budget:real. 0 < budget ==> budget < 2 * budget` is answered `!x:real. 0 < x ==> x < 2 * x`, and
`x, y, z` survive as often as they do only because they are the first three names `Show.freshName`
reaches for. That is not a defect in the printer and the printer cannot repair it: the name is not
in the object being printed.

What it costs is checking, which is the thing a formal statement is for. A statement has to be
checkable against the informal claim it translates by a reader who did not write it, and a report
whose binders the printer named has made its own answer harder to check than the claim it answers.
`Ask` pays back the cheap half by printing the claim as the caller wrote it beside the report
wherever the two differ, which costs a string it already held. The expensive half, a name hint
carried beside the term from the reader through `Cost` to the renderer, is **not** built, and the
count that decided it was taken on 2026-09-12: of the consumers that render a report, exactly one
besides the command line takes a claim as somebody's own text, which is `Argument`, and it held
that text one method above its renderer, so the same cheap move covers it and no hint has to
travel. Every other consumer -- `Propose`, `Sweep`, `Novelty` -- is handed claims a generator built
out of theorems, where there is no author's name to lose.

Both halves of the cheap move are built, and the gap between them is worth leaving in the record.
This paragraph named `Argument` as covered at 15:38 on 2026-09-12 and `Argument` did not print the
caller's text until five and a half hours later: `read` parsed each text and dropped it. A sentence
in the present tense about work that has not happened reads exactly like one about work that has,
and an architecture decision record is the kind of document a later reader believes without
checking. What closed it was reading the sentence and going to look.

The expensive half becomes worth building when something drives this system with text it wrote and
reads the answer somewhere the text is gone, and nothing does yet.

What this does not cover: the representation removes capture, not every substitution bug. A rule
that opens with a variable already free in the surrounding hypotheses is still wrong, and nothing
in the representation stops it; freshness remains the caller's obligation.

## Alternatives rejected

**Named variables with capture-avoiding substitution.** What HOL Light does, and it demonstrably
works, so this is not a claim that the option is unsound. It loses because the two functions that
implement it, the capture-avoiding substitution and the alpha comparison, are where
name-based implementations concentrate their hardest bugs, and here they would sit in the trusted
base where a bug is unbounded. The rejection is about where the risk lands, not about whether the
technique can be done correctly.

**Pure de Bruijn, free variables as indices too.** Makes alpha-equality structural as well, and is
the smallest representation. It loses because a theorem then only means something relative to a
context, and instantiating a theorem into a different context requires shifting every index in
it. Shifting code is exactly the class of error this decision is trying to remove, and it would
have to be correct in the kernel and in every rule that moves a theorem between contexts.

**Higher-order abstract syntax, binders as host-language functions.** Substitution becomes
application and is correct for free. It loses because terms stop being inspectable data: you
cannot pattern match under a binder, cannot serialise a proof, and cannot write the printer, all
of which this system needs.
