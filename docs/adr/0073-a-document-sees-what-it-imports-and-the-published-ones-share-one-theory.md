# 0073. A document sees what it imports, and the published ones share one theory

- **Status:** accepted, takes up increment 3 of 0070
- **Date:** 2026-11-11
- **Card:** Mycelium `c3806ddb`

## Context

`docs/adr/0070` put publication in a module above `tactics` that "replays [the documents] in
dependency order into one theory", so that a name declared twice is refused by the kernel as it is
in a session. It did not say what a document sees while it is checked, how an import is resolved,
or what the price of a theorem names when the proof uses a theorem of another document. Writing the
first two published documents, `Doubling` and `Parity`, made each of those a decision.

## Decision

**A document is checked in a theory of its own: the chain's widest, with the definitions of the
documents it imports, directly or through another import, made again in the order they were
checked.** Its facts are those documents' theorems beside the library. A document it does not
import is not there, even when it was checked earlier in the same run. A definition made again is
the same constant, because a defined constant carries its definition (`docs/adr/0008`), so a
theorem proved where the imported document was checked is about the constant the importer reads.
`PublishedSpec` asserts that of every published theorem against the one theory with
`Derivation.foreignTo`, and asserts the control: against the chain alone, the same theorems are
foreign.

**Publication then makes every published definition again in one theory**, in the order the
documents were checked, and refuses what that theory refuses: a name two documents both define,
even when neither imports the other. A theorem name two documents both declare is refused beside
it, since a theorem adds no name to a theory and the kernel cannot see that clash. The one theory
is compared with the chain's and must assert the same axioms.

**An imported theorem and a document's own earlier theorem enter a proof as citations**
(`Kernel.cite`, `docs/adr/0047`), and the price stops at them: `library facts` and `inferences` are
the proof's own, and `imported` names what it cited from other documents as `DOCUMENT.NAME`. A
cited fact is identified by the name its citation carries and not by its statement, because two
facts can state one thing; the first version keyed by statement and reported `B.USES` for a proof
that cited `A.TWICE_N_ZERO`, which `WorkspaceSpec` caught.

**A declaration may not take the name of a library lemma or of an imported fact.** A name is a fact
once declared, and the lookup order (the proof, the document, its imports, the library) means a
document's `ADD_SYM` would hide the library's from every later proof citing it.

**The checker command moves to the publication module**, as `published.Check`, because an import
may name a published document and only a module above that one can read them. What it does stays
in `tactics.Check.run`, tested beside the elaborator, which takes the published documents as a
function. A published name wins over a file of that name beside the document checked, and the
command says so on its error stream.

**`cases h from F` joins the language**, splitting a fact `F : A \/ B` into branches `left` and
`right`. `Parity` needed it, and a disjunction already held could not be taken apart before:
`cases h : P` splits on excluded middle, and `auto` refuses `A \/ B, ~A |- B` when the atoms are
equations, routing the goal to `RING` by its shape.

## Alternatives rejected

- **One theory growing as documents are checked**, which is the reading of 0070 that costs
  nothing to build. A document would then see every constant of every document checked before it,
  so its imports would stop saying what it rests on, and whether it checks would depend on the
  order somebody ran things in.
- **Checking each published document once, in the one theory, after its imports.** It refuses a
  name clash, and it has the visibility problem above in the order of `Published.Names`.
- **Leaving the price's walk as it was for a document's own facts.** The walk entered them, so a
  proof using an earlier theorem listed every library lemma that theorem's proof had used, which
  contradicts what `docs/language.md` said `library facts` means. The inference count of such a
  proof is now smaller, which is the measurement being right rather than the proof changing.
- **The command staying in `tactics`, resolving imports beside the file only.** A published
  document would then be importable only from inside the repository's resource directory, which
  makes publishing something nobody outside can build on.

## Consequences

- The published theorems are a library of their own, `Published.standard.library`, and
  `docs/published.md` is its page. `auto`, `find` and `Ask` still search the chain's library;
  reaching the published one from them is not this decision.
- `docs/language.md` describes imports, `cases h from F` and publishing, and its examples include
  two named documents that import each other, checked together by `LanguageSpec`.
- The modules are twelve, and the coverage gate finds the new one by its directory.
