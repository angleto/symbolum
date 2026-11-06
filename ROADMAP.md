# Roadmap

**EXCERPT — for anyone scanning the index:**
The work ahead, grouped by what it is for: the incompleteness theorems, the ladder of theorems
the showcase climbs, the prover's automation, the trusted base nobody has read yet, distribution,
and the build. What has been reached is [docs/where-it-stands.md](docs/where-it-stands.md); this
file says only what is next and what blocks it.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

The live plan is a task board outside this repository. This file is a snapshot of its open items,
taken on 2026-11-06, and it is rewritten as a whole when it is refreshed rather than patched line
by line. It carries no counts on purpose: a figure about the library or the corpus belongs where
the code can check it, and a roadmap is not that place.

## 1. Goedel's second incompleteness theorem

The declared goal of the proof side. The embedded theory is Peano arithmetic and syntax is coded
with the beta function ([docs/adr/0013](docs/adr/0013-the-embedded-theory-is-pa-and-the-coding-is-the-beta-function.md));
the object syntax, the bounded quantifiers
([docs/adr/0021](docs/adr/0021-the-derived-connectives-are-constants-that-build-codes.md)) and a
provability predicate `NUM_PROV` with its closure rules are in the library.

Next, in order:

- **Arithmetise `Prov` in the object language**, so that provability is a formula of PA and not
  only a predicate of the meta-theory. In progress.
- **The derivability conditions**: D1 (what PA proves, PA proves it proves), then the diagonal
  lemma, then D2 and D3 at the object level.
- **G1 and G2.**
- **That the decoding is Delta-0 in the object theory**, which `docs/adr/0014` claims and does not
  prove. It is the last item because everything above it can be written without it.

## 2. The showcase ladder

The showcase ([docs/theorems.md](docs/theorems.md)) is a diagnostic instrument as much as a
gallery: a theorem that cannot be stated names a missing primitive, and one that cannot be proved
names a missing procedure. The gap it exposes is the work, and it is not routed around.

- **Done:** elementary number theory up to unique factorisation and Fermat's little theorem;
  analysis up to the intermediate and mean value theorems, l'Hopital, the fundamental theorem of
  calculus and the fundamental theorem of algebra.
- **Next: Hilbert's tenth problem.** Matiyasevich's theorem is a statement about Diophantine
  definability, and the beta function, sequence coding and arithmetised syntax the Goedel work is
  laying are the same ground floor. It is the one item on the list the current work walks toward.
- **Blocked by a decision, not by size: the four colour theorem.** The only known proofs check
  hundreds of configurations by computation, and
  [docs/adr/0010](docs/adr/0010-no-computing-rule-in-the-kernel.md) keeps a computation rule out of
  the kernel while the size of the trusted base is the argument. Taking it on means reopening that
  record first.
- **Exploratory:** Gilbreath's conjecture read as an absorption mechanism, measuring it and proving
  the part that can be proved; and small certified results requested by other projects.

## 3. The prover's automation

- **Nonlinear inequalities past degree two.** `Linarith` reaches squares of linear forms
  ([docs/adr/0056](docs/adr/0056-the-second-source-of-squares-is-a-gram-matrix-and-needs-no-search.md)).
  Beyond that a form has many Gram matrices and choosing a semidefinite one is a search, which
  belongs outside the trusted boundary with only its certificate checked inside. These are among
  the miniF2F statements the tactic surface still cannot settle
  ([docs/adr/0029](docs/adr/0029-the-corpus-asks-for-arithmetic-and-not-for-saturation.md)).
- **A width lower bound for resolution refutations of the pigeonhole principle**, proved in the
  kernel: a piece of the Cook-Reckhow programme in proof complexity, and not a claim about P and
  NP.
- **The interface of the reals:** whether `inv 0 = 0` is published under a name of the reals'
  own, since today it exists only as a fact about cuts. A decision about the interface.

## 4. The trusted base, read by a person

[docs/reading-register.md](docs/reading-register.md) lists every axiom, every defined constant,
every law of the reals and every row of the precedence table, and says of each whether a person
has read it against a source. None has been. The kernel's inference rules have the same status.
Reading them is work no test can do, and the register says why a test that seemed to would be
worse than none.

## 5. Distribution

The library is published on GitHub Packages, which asks every reader for a token, even for a public
package. Publishing to Maven Central (signing key, verified namespace, release process) is what
makes the coordinates usable by a project that has never seen this repository.

## 6. The build

- The coverage gate in CI runs into the job's time limit, so on those runs the floors are never
  asked, and the gate says so rather than passing.
- The test fork of `tactics` runs close to its heap limit, the tightest memory margin in the build.
- **A tool to draw cellular automata and difference tables as images**, proposed for the
  developments about Rule 30 and Gilbreath's table.
