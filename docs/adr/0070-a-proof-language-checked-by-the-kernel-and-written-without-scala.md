# 0070. A proof language, checked by the kernel and written without Scala

- **Status:** accepted
- **Date:** 2026-11-10
- **Card:** Mycelium `c3806ddb`

## Context

A theorem enters this repository today in one way: somebody writes Scala that drives the kernel.
The statement is text in the term language, the proof is a sequence of calls into `Rules`, `Conv`,
`Rewrite` and the procedures, and the file joins a link of the chain. That is the LCF arrangement,
the one HOL Light uses, and it is sound for the reason it always is: the Scala is untrusted, and
only the kernel can construct a `Kernel.Thm`.

What there is without Scala is the notebook, and measured on 2026-11-10 at `ab5ed2ca` it falls short
of a proof language in two ways:

- **`derive` offers five inferences**: `specialise`, `mp`, `left`, `right`, `both`
  (`Session.Surface.Inferences`). It has no induction, generalisation, discharge, case split or
  arithmetic, so a proof by induction cannot be written at all.
- **A session publishes nothing.** `Session` lives in `tactics`, and the library is the chain built
  in `theories`, one floor below. A fact proved in a session cannot reach the library without
  inverting the module graph.

The request is a surface that is better than Lean at something, and clear and usable enough that a
reader does not go back to Lean, rather than a thin wrapper around the existing calls. That bar
decides most of what follows, so it comes first.

## What the bar means, and what it does not

**Being better than Lean 4 with Mathlib in general is not reachable, and this record does not
claim it.** At this date the library holds 1117 lemmas (`docs/lemmas.md`), and Mathlib holds two
orders of magnitude more. The logic is simple type theory, not the calculus of inductive
constructions, so there are no dependent types: a subtype is a `typedef` with its bijection
(`docs/adr/0006`). Editor tooling and a community do not come out of a design document. A
development that needs Mathlib-scale mathematics, or dependent types, belongs in Lean.

**What the language has to match** is what makes Lean usable. A language that lacks any of these
is the accrocchio this record exists to avoid:

1. **Structured proofs with named cases.** `induction n with | zero => ... | succ n ih => ...`,
   `have h : P := by ...`, `obtain`, `calc`, `show`, and a step that names what it proves. A goal
   stack where each command silently acts on the first open goal, which is HOL Light's `e(...)`,
   is the style Lean and Isar replaced, and it is not offered.
2. **Error recovery.** A failed step does not stop the checking. The proof it was in is reported
   incomplete, that goal is reported as the failure, and every other step and every other theorem
   of the document is still checked. An incomplete theorem is published as nothing.
3. **The goal at every point.** In the editor through a language server (Neovim and Zed both speak
   LSP), in the notebook, and in the checker's output.
4. **Automation that closes routine goals**: rewriting with a named lemma set (`simp`), the
   decision procedures the repository already has (`RING`, `LINARITH`, `Field`, `numLin` over the
   naturals, the propositional procedures, `Chaining`), and `auto`, which is the tactic surface
   `Prove` behind one word.
5. **Documents with imports, definitions and datatypes**, checked incrementally.

**What makes it worth using instead of Lean** is what this repository already has and Lean does not
have in one place. Each item is a commitment the implementation is tested against:

- **A false step gets a counterexample, not "tactic failed".** When a `have` or a goal does not
  close, `Refutation` is asked before the refusal is written, and the answer carries which of its
  seven cases it is. "Sampling found a point where it is false" and "no point answered" stay two
  different messages (`docs/adr/0005`). Lean's `plausible` is a separate tactic somebody has to
  think of calling.
- **The price of a theorem is part of the result.** At `qed` the checker prints what the theorem
  rests on: the axioms, through `Derivation.axiomsOf`, and the assumptions of the document, through
  `Derivation.foreignTo`. Lean has `#print axioms` on request.
- **The algebra side proposes, the kernel checks.** A step can ask `core` for a rewrite chain and
  have each link certified. That is the loop `docs/adr/0003` describes, reached from a proof
  rather than from Scala.
- **Every refusal is a value with a next step** (`Remedy`), and the checker can print the whole
  report as structured output, so an LLM session driving the checker reads a field instead of
  parsing prose.
- **A published document cannot add a belief.** `assume` is accepted in a session and refused in a
  document headed for the library, so a domain assumption can only reach the library as the
  hypothesis of a theorem.

## Decision

### The language

A document is a sequence of declarations: `import`, `define`, `datatype`, `theorem`. Terms keep
the existing term language and its parser, so a statement reads as it does in `docs/lemmas.md`. A
proof is a block, and its cases are named in the text, never chosen by the position of a goal:

```
theorem ADD_ZERO_LEFT : !n:num. 0 + n = n
proof
  fix n
  induction n
  case zero:
    simp
  case succ m ih:
    calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
         _         = SUC m       by rewrite ih
qed
```

The steps are `fix`, `assume`, `have NAME : P by METHOD` (or with a nested proof block), `show P`,
`obtain x h from FACT`, `cases NAME : P`, `induction x [using LEMMA]` with named cases, `calc`,
`apply LEMMA`, `exact FACT`, and `witness t`. The methods are `simp [L1, L2]`, `rewrite L1, L2`,
`ring`, `linarith`, `arith` (`numLin`), `auto [from F1, F2]`, `exact`, and the combinators `then`
and `first`. Delimiters are keywords rather than indentation: an LLM writing a document gets
indentation wrong more often than it gets `qed` wrong, and an indentation error that reparses as
something else is a translation the reader cannot see.

### The architecture

- **The elaborator lives in `tactics`.** That module is the lowest one that sees both halves, and
  the CAS-proposes step needs `core`. Every step becomes calls to `Rules`, `Rewrite` and the
  procedures, and the theorem is the kernel's. The trusted base does not move.
- **One elaborator, three front ends.** The checker command, the notebook and the language server
  all fold the same document through the same elaborator, so the goal a reader sees in the editor
  is the goal the checker saw.
- **Publication is a new module above `tactics`.** It holds the published documents, replays them
  in dependency order into **one** theory, and exposes their theorems as a library link with a
  generated page and a gate, which is the same arrangement `docs/lemmas.md` has. One theory is what
  keeps `SoundnessAttackSpec`'s argument valid: a name declared twice is refused by the kernel's
  `AlreadyDeclared`, as it is in a session today.
- **The language server is its own module**, so its one external dependency, an LSP library, sits
  in nothing the prover needs.

## Alternatives rejected

- **Extending `derive` with more inferences.** It stays a forward, one-line, Hilbert-style surface:
  the caller writes the induction predicate as a lambda and discharges by hand. It does not meet
  point 1 above.
- **A goal stack of line commands in the session.** This was the first candidate, and work started
  on it on 2026-11-10. It fails points 1, 2 and 3: cases are positional, a refused line leaves the
  next lines acting on a goal their author did not mean, and nothing shows the goal in an editor.
  What it left behind and this record keeps is the parser change. A proof that has fixed `n : num`
  reads `n` at that type, through `Parser.term(theory, notation, text, expected, fixed)`, and
  every design needs that.
- **Scala as the proof language, through scripts.** A Scala cell can reach `Kernel.assertAxiom`,
  and then nothing on the page is a function of the page (`Session.Command`'s own comment).
- **Writing the library in Lean and importing it.** It moves the kernel. Sharing a statement
  between two systems is a translation nobody checks, and that is `docs/adr/0003`'s whole point.

## Consequences

- The work is in increments, each of which ends in something that proves a theorem end to end:
  1. the parser for documents and the elaborator core, with error recovery, the checker command,
     and the structured report;
  2. refutation on failure, and the price at `qed`;
  3. the publication module, its generated page and its gate;
  4. the language server;
  5. the notebook on the same elaborator;
  6. `simp` sets and `datatype` from the language.
- **It is done when** a sample of the library's theorems proved by induction in Scala today
  (51 main sources in `theories` mention induction) is rewritten as documents and checks to the
  same statement. The sample is drawn by a rule written down before it is drawn, not chosen.
