# 0059. The sixteen are laws: `axioms` names only what a theory asserts

- **Status:** accepted, extends 0053
- **Date:** 2026-10-05

## Context

[`0053`](0053-the-sixteen-are-theorems-and-real-is-the-cut-type.md) proved the sixteen statements of a
complete ordered field about the cuts on the rationals and kept every consumer working unchanged:
`RealTheory.axioms` still held a map from the sixteen names to theorems, `RealTheory.axiom(name)`
still answered, and `Real.Axioms` was still the list of their texts. The program that phase closed,
Mycelium card `fa8737ad`, had asked for the opposite in the same change: that `RealTheory` stop calling
that map `axioms`. `0053` did not record the choice among its alternatives.

What the kept name says after `0053` is false in one place that matters. A `RealTheory` carries two
maps a reader would call its axioms, `reals.axioms` and `reals.theory.axioms`. The second is what
the kernel holds as asserted: choice, eta and infinity. The first held sixteen theorems. Of the four
classes with an `axiom(name)` accessor (`Classical`, `Natural`, `Domain`, `RealTheory`), `RealTheory`
was the only one whose map held anything that was not asserted. `Natural.Axioms` holds infinity alone,
which `Natural` asserts.

## Decision

**The sixteen are the reals' laws, and the accessor says so.** `RealTheory.axioms` is `laws`,
`RealTheory.axiom(name)` is `law(name)`, and `Real.Axioms` is `Real.Laws`. The names of the sixteen
(`ADD_SYM` through `COMPLETENESS`), their statements and their printed forms do not move, which is
the property `0004` preserved for this step and `RealSpec` pins.

**`axioms` names only what a theory asserts**, everywhere in the repository: `Theory.axioms`,
`Classical.Axioms`, `Natural.Axioms`, and a domain's assumptions. That is what makes the rename one
sentence rather than a convention to remember: a reader who meets `axioms` is reading the trusted
base.

"Law" is the word the code already used for the sixteen read as an interface: `Cost.Report.laws`,
the line "of the sixteen of the reals" it prints, and `Real.spent`, which stops a report at them.

## Consequences

**The rename was found by the compiler, not by a search.** `axiom(` is a method of four classes and
a search for it cannot say which receiver a call has. The change was made at the positions the
compiler reported as missing members of `RealTheory` and `object Real`, round after round until
`Test/compile` passed, and nothing else was edited by pattern.

**Documents that described the sixteen as axioms say what they are now.** The second entry of
`docs/architecture.md`, quoted in `docs/reading-register.md` and in `Register.scala`, said a
mis-stated one makes everything provable. That stopped being true with `0053`: a law false of the
cuts fails to be proved and the construction refuses to build. What is still true, and what those
three places say now, is that nothing but a reader checks that the sixteen state a complete ordered
field.

**What this does not repair.** The sixteen have had no row in `docs/reading-register.md` since
`0053`, because that register reads its first population off `theory.axioms`. That is a gap and
not a consequence of this decision, and it is Mycelium card `f327c976`.

## Alternatives rejected

**Keeping `axiom` in the sense of "an axiom of the structure".** It is a correct sense in
mathematics: the sixteen are the axioms of a complete ordered field, and the construction is a model
of them. It was rejected because this repository uses the word for the other sense everywhere else,
and the two senses met in one object: `reals.axioms` and `reals.theory.axioms` would answer
different questions under the same name, and the one a reader reaches first is the one that is not
the trusted base.

**Renaming the map and keeping `axiom(name)`.** Every one of the call sites asks for one of the
sixteen by name, so the accessor is where the false word is read. A field renamed under an
accessor that still said `axiom` would leave the call sites as they were.
