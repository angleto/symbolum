# 0074. A notebook cell is a declaration of the proof language

- **Status:** accepted, takes up increment 5 of 0070, before increment 4
- **Date:** 2026-11-11
- **Card:** Mycelium `c3806ddb`

## Context

`docs/adr/0070` asked for one elaborator with three front ends, the checker, the notebook and a
language server, and listed the notebook fifth, after the language server. The notebook is the
surface already in use, and it needs no editor configured, so it comes first: this record is
increment 5 and increment 4 is still to come.

Until now a session had its own commands, one line each, and none of them was the language: a proof
by induction could not be written in a notebook at all. Three things had to be decided. Where a
multi-line declaration ends among one-line commands. What a declaration checked in a session sees.
And what `import` means in a session, which holds one theory that only grows.

## Decision

**`theorem` is a command of the session, read by the document reader and checked by the elaborator
the checker uses** (`Elaborate.within`). It is checked in the session's theory as it stands, with
what the session declared, defined and assumed. The session's named facts are held as a document's
own earlier theorems are: as citations, so a price stops at them and lists them under `from this
session`. What a session assumed still reaches the theorem through the citation and is named on
the cell, as every session theorem's is. A proof that does not check is shown with every problem
and the goal at each, as the checker shows it. The session gains nothing from it.

**A theorem runs to the `qed` that closes it** (`Document.extent`), counting the `proof ... qed` of
every `have` and `show` inside, and to the end of the submission when it is never closed. A theorem
whose line ends in `by` is that line. The boundary is the reader's own keyword structure and not the
first word of the next line. `show` and `assume` are both commands of a session and steps of a
proof, so a rule reading first words would cut a proof in the middle. `DocumentSpec` compares
`extent` with where the reader ends each theorem, on every proof in `docs/language.md` and in the
published documents.

**`import NAME` takes a document into the session whole, or not at all.** The document and what it
imports are checked by `Workspace` over the chain, as the checker checks them. Their definitions are
then made again in the session's theory, which gives the same constants (`docs/adr/0008`). Their
theorems become facts the session holds, each priced as `DOCUMENT.NAME`. Any refusal leaves the
session as it was: a document that does not check, a definition the session's theory refuses, a
fact whose name the session already holds. A session holding half a document would hold theorems
about constants it does not have. A document already imported is not imported again. An `import`
written inside a `theorem` cell is refused on its line, because it would change the theory partway
through a cell.

**The notebook's command moves to the publication module**, as `published.Notebook`, for the reason
the checker's did (`docs/adr/0073`): a session imports the published documents, and only a module
above them can read them. `tactics.Notebook.run` takes the session as a parameter. The distribution
ships `published.Notebook` and, for the first time, the checker, as `bin/symbolum-check`.

**The box is a `<textarea>`**, where Enter runs the cell and Shift+Enter starts a new line, so a
theorem and its proof can be typed as one cell. A paste of several lines is still one submission,
and its lines are still run in order. The server no longer trims each line, so a proof keeps its
indentation in the transcript.

## Alternatives rejected

- **Grouping lines by the first word**, which is a line's keyword in a session. It cuts every proof
  that uses `show` or `assume` as a step.
- **One `document` cell holding several declarations.** A transcript is a list of commands, and a
  cell holding a document would need a delimiter of its own to replay. One theorem per cell needs
  none, since `qed` already is one.
- **`define` through the elaborator as well.** The session's `define` has the same syntax and the
  kernel checks it the same way, and the elaborator does not hand back the wider theory it builds.
  So the difference would be the rule that a name of the library cannot be taken, which a
  session's `define` and `prove` do not apply today. That is recorded here, and changing it is not
  this decision.
- **Importing what an imported document did prove when part of it fails**, as `Workspace` does for
  a document. A document is repaired in its file, and its importer is checked again. A session
  cannot repair a published document, and a half-imported session leaves nothing to check again.

## Consequences

- `Session.Command.Keywords` gains `theorem` and `import`, and `AGENTS.md` lists them, as
  `DocumentationSpec` requires.
- `Session.Outcome.Proved` carries the elaborator's price, and `Session.Outcome.Incomplete` carries
  the problems of a proof that did not check.
- `prove` and `derive` remain. `prove` is a claim put to the tactic surface with no proof written,
  and `derive` is one inference by hand. Both are cheaper to type for what they do.
- The page's JavaScript is not run by any test here, as `Notebook` already says. The server's half
  is covered by `SessionLanguageSpec`, and `NotebookSpec` covers it over a socket.
