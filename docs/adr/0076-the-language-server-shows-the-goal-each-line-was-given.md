# 0076. The language server shows the goal each line was given

- **Status:** accepted, increment 4 of 0070
- **Date:** 2026-11-12
- **Card:** Mycelium `c3806ddb`

## Context

`docs/adr/0070` asked for the goal at every point "in the editor through a language server (Neovim
and Zed both speak LSP), in the notebook, and in the checker's output", and put the language server
in a module of its own so that its one external dependency, an LSP library, sits in nothing the
prover needs. Increments 1, 2, 3 and 5 gave the checker and the notebook the elaborator. Until this
record the elaborator kept a goal only where a step failed, so a proof that checked had no goal to
show at any of its lines, and an editor had nothing to show while a proof was being written.

## Decision

**The elaborator records the goal each line of a proof was given** (`Elaborate.Goal`,
`Entry.goals`, `Entry.goalAt`). The record is made where the line is handled. The `proof` line gets
the claim, each step the goal it acts on, before it acts, each branch header the goal of its case
with the names it introduced, and each link of a `calc` the relation that link proves. Each step's
goal is recorded before the step acts, so `fix n` shows the goal without `n`, and the line after
it has `n`. A line that no
step starts on, `qed` or a blank line, shows the goal of the step above it. A proof that does not
check records its goals as far as it was checked, because recovery goes on past a failed step. The
goals ride on `Elaborate.Checked` beside the problems and the notes, so the elaborator holds no
state for them. The checker's `--json` carries them too, which is the "checker's output" of 0070.

**The server is the module `lsp`, above `published`**, because a document an editor opens may import
a published one. It is not published to the registry: it is a program an editor starts, and it
ships in the distribution as `bin/symbolum-language-server`. `Analysis` holds everything it says as
functions of the text, and `Server` is the protocol around them. It offers three things:

- **diagnostics**: every problem of the checker's report on its line, in the checker's words;
- **hover**: the goal at the line under the cursor, and on a declaration's first line its status
  and price;
- **document symbols**: each declaration over the lines `Document.extent` gives it.

Each answer comes from the same report the checker prints, so an editor and the checker cannot
disagree about a document.

**Imports resolve as the checker resolves them, with the editor's text in front of the disk.** A
published name reads the published document. Any other name reads the document of that name beside
the importer as the editor holds it, and the file on disk when it is not open. A change to an open
document checks again every open document in its directory. A file beside the document with a
published name is not read, and a warning on the import line says so, where `Check` says it on
its error stream.

**Standard output belongs to the protocol.** `LanguageServer.main` takes the stream for lsp4j
before anything runs and points `System.out` and `Console.out` at standard error. A `println` left
in a procedure would otherwise end an editor's session with a malformed message.

**The library is lsp4j 1.0.0, taken under the Eclipse Distribution License 1.0.** lsp4j's
repository licenses it under the Eclipse Public License 2.0 or the EDL 1.0. The EDL is the 3-clause
BSD licence, compatible with the AGPLv3 as `docs/adr/0068` finds the other dependencies. The EPL 2.0
alone is not, since this repository names no secondary licence for it, which is why the choice is
written here. Its POM declares only the EPL 2.0, and the `about.html` in its jar is the Eclipse
template naming the EPL 1.0. The repository's own `LICENSE`, read on 2026-11-12, gives both
alternatives. lsp4j brings `gson` and `error_prone_annotations`, both Apache 2.0. Verified working
before this was recorded: Neovim 0.12, headless, against the staged distribution, showed a
diagnostic with its goal, a hover with the goal of a failing step, a hover with the price of a
theorem citing an imported published fact, and the outline.

## Alternatives rejected

- **The JSON-RPC written by hand.** It is a few hundred lines that lsp4j has, tested. The
  dependency is what 0070 already agreed to, in the module 0070 put it in.
- **The goal after each step instead of before it.** A reader on `fix n` asks what the step is
  about to act on. The goal after it is the next line's.
- **Re-elaborating to the cursor on every hover.** It costs a check per hover, and it would give an
  answer nothing else in the system computes. The recorded goals come from the run that produced
  the diagnostics, so the hover and the diagnostics cannot disagree.
- **Completion and go-to-definition in this increment.** Neither is in 0070's list of what makes
  the language usable, and each would need an index of names this increment has no other use for.
- **A Zed extension.** Zed starts a server only for a language an extension declares, and an
  extension is a repository of its own with a tree-sitter grammar. It is named as missing in
  `docs/language.md` rather than half-done.

## Consequences

- `Elaborate.Checked` gains `goals`, and `Elaborate.Entry` gains `goals` and `goalAt`. The price
  and a problem are each formatted in one place now (`Price.lines`, `Problem.detail`), where the
  checker and the notebook had two copies.
- The distribution's launchers gain `bin/symbolum-language-server`, and `LauncherSpec` lists its
  main among those that cannot be entered, since it serves until the editor closes it.
  `ServerSpec` speaks the protocol to `Server` over pipes instead.
- `StyleSpec` lists the server's one `AtomicReference` with the reason it is there.
