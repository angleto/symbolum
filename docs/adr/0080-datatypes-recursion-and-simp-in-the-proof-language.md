# 0080. Datatypes, recursion and `simp` in the proof language

- **Status:** accepted, increment 6 of 0070
- **Date:** 2026-11-12
- **Card:** Mycelium `c3806ddb`

## Context

`docs/adr/0070` listed what a proof language has to match to be usable, and two of the items were
still missing after five increments. One was automation that closes routine goals, "rewriting with
a named lemma set (`simp`)". The other was "documents with imports, definitions and datatypes".
The language had conservative definitions and nothing else. A development about trees or lists
could not be written as a document, and every routine step was a `rewrite` naming each equation
it used.

The repository already had the machinery underneath. `Datatype` (`docs/adr/0042`) builds an
inductive type from a list of constructors, with its induction, case analysis, recursion theorem,
injectivity and distinctness, all derived. `Datatype.defineRecursive` names a function from that
recursion theorem. `Rewrite` rewrites to a normal form and refuses a walk that did not reach one.
What was missing was the language reaching them.

## Decision

**`datatype NAME = C1 | C2 T1 T2` declares a type through `Datatype`, unchanged.** The arguments
are types read by the term parser's type reader. An argument written as the type itself, with its
own parameters, is the recursive one. The type's facts are the document's, under the names
`Datatype` gives them, and a name one of them would take from another declaration is refused.
`induction x` over a value of the type uses its principle, and the branches are named by the
constructors, so `case NODE l x r ihl ihr:` reads as Lean's `| node l x r ihl ihr =>`.

**`define NAME : TYPE`, one equation per line, then `end`, defines a function by structural
recursion** (`tactics/Recursive.scala`). The equations are read with `NAME` as a variable of the
type given. They are checked to be structural, turned into the clauses `defineRecursive` takes,
and the equations it proves are brought back to the form written and compared with it. A
definition that is not what was written is refused, never accepted as something nearby. Parameters
before the matched argument must be the same in every equation. Arguments after it may vary,
which the clause supports by returning a function of them. So `APPEND` and accumulators are
definable, and the matched argument may sit anywhere after the parameters.

**`simp` is `Rewrite` to a normal form with a set of rules nobody names at the step**
(`tactics/Simp.scala`). The set holds:

- the clauses of the connectives, stated as text and proved by the tactic surface when the
  elaborator is built;
- the freeness of `num` and the equations that define `+` and `*` (`Simp.Base`);
- the injectivity and distinctness of every datatype in scope;
- the equations of every function defined by recursion;
- every theorem marked `[simp]`, in this document or in one it imports.

`simp [F, G]` adds facts at the step, the proof's own included. It is a step that changes the goal,
as `rewrite` is, a method that closes it, and the first half of `simp then M`. A refusal says what
was left, and a walk that hit the step limit is refused as `rewrite`'s is, never taken as a normal
form.

**A fact is turned into rules by inference, and only in the shapes listed.** An equation stays an
equation. A conjunction becomes its conjuncts. `~P` becomes `P = F`, and `(b = a) = F` too when
`P` is `a = b`. A constructor's injectivity becomes the equation between its sides. Any other
proposition `P` becomes `P = T`. An implication of another shape is a conditional equation, which
`Rewrite` does not apply. It is refused, on the `[simp]` declaration before the proof is checked,
or at the step. `rewrite` takes only the first two readings: the shape is decided by `simp`, which
owns a set, and a `rewrite` turning a hypothesis into `P = T` would quietly rewrite with a fact its
writer named by mistake.

**A declaration records what it made, and an importer makes it again through one function**
(`Elaborate.Made`, `Elaborate.make`). Before this record three places remade an imported
definition, each from a body read back out of its defining equation: the checker's imports, the
published library and the notebook's import. A datatype has no defining equation to read a body
from, and a recursive function's body is a choice term nobody should rebuild by hand. So each
declaration carries its description: a constant's body, a datatype's specification, or a recursive
function's clauses. The three places call `make` on it. Made again from the same description, it is
the same constant or type, since a defined constant carries its definition and `Datatype` is a
function of its specification. `InductiveSpec` checks this with a document that proves a theorem
about another document's datatype and function, by its induction and its `simp` set.

## Alternatives rejected

- **A `simp` set chosen from the library by a naming rule**, every `*_ZERO` and `*_SUC` equation
  for example. It is what Isabelle's `primrec` amounts to, and over this library it would bring in
  equations nobody chose, by a selector whose reach nobody measured. `Simp.Base` is six names, and
  a document grows the set by marking what it proves.
- **Conditional rewriting.** It would let `simp` use an implication, and it is a change to
  `Rewrite`, with its own termination argument about discharging conditions. Nothing in this
  increment needed it, and refusing such a fact says what is missing.
- **Recursion through a well-founded relation.** It would need a measure, a proof obligation per
  call, and a different construction from the recursion theorem. Structural recursion is what a
  datatype gives without one.
- **`simp A, B` without brackets, as `rewrite` is written.** 0070 wrote `simp [L1, L2]`, and the
  brackets say that the facts are added to a set, where `rewrite`'s list is the whole set.

## Consequences

- The six increments of 0070 are written. What 0070 calls done is a sample of the library's
  inductive theorems rewritten as documents, by a rule written down before the sample is drawn, and
  that is the next work on card `c3806ddb`.
- `Elaborate.Entry` gains the facts a declaration provides beyond its own name, the names among
  them in the simp set, and what it made. `Kind` gains `Datatype`.
- A notebook cell does not declare a datatype: a session reads the datatypes of the documents it
  imports, and `induction` in a theorem cell uses their principles.
- What a `simp` rewrote with is read in the price like anything else a proof cites: a document's
  function cited by `simp` appears under the document's theorems, a library equation under the
  library's.
