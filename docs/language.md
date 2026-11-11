# The proof language

**EXCERPT — for anyone scanning the index:**
How to write a proof without Scala: a document of definitions and theorems with structured proofs,
checked by the kernel through `published/runMain garden.xeno.symbolum.published.Check FILE`. Every
step, every method, what a report says, how one document imports another, how a document is
published into the repository's library, and what the language does not do yet. The decision is
`docs/adr/0070`; every example in this file is checked by `LanguageSpec`.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## What it is

A document is a sequence of `define` and `theorem` declarations, after the `import` lines naming
the documents it builds on. A theorem is a claim in the term
language, the one `docs/lemmas.md` is written in, and a proof made of steps, one per line. The
checker turns each step into calls to the kernel's rules and to the decision procedures. The
theorem at the end is the kernel's, so the checker can refuse a proof but it cannot accept a false
one.

```sym
-- The left identity of addition on the naturals, by induction.
theorem ADD_ZERO_LEFT : !n:num. 0 + n = n
proof
  fix n
  induction n
  case zero:
    by rewrite NUM_ADD_ZERO
  case succ m ih:
    calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
         _ = SUC m by rewrite ih
  end
qed
```

## Checking a document

```
tools/sbt "published/runMain garden.xeno.symbolum.published.Check path/to/file.sym"
tools/sbt "published/runMain garden.xeno.symbolum.published.Check --json path/to/file.sym"
```

An import naming a published document ([published.md](published.md)) reads that one, wherever the file is.
Any other import is read from the file's own directory: `import Geometry` is `Geometry.sym` beside
it. A file beside it with a published name is not read, and the checker says so on the error
stream. An imported document is checked too, and is not printed; a problem in it is reported on the import
line, and that line names the file to check next.

For every declaration the report gives its line and its status, which is one of `proved`,
`defined`, `incomplete` or `refused`. A declaration that did not check lists its problems. Each
problem has the line it is on, the refusal, a `try:` line with the next thing to do, and the goal
as it stood at that step:

```
line 22: theorem BROKEN: incomplete
  line 25: x is not equal to 1 + x
    try: nothing mechanical follows: x and 1 + x both reached a normal form and the forms differ
    false: settled: a point where the claim fails: x=-0.5147186257614291
    x : real
    |- x = x + 1
```

### Whether a goal that did not close is false

When a method refuses, the checker asks `Refutation` about the goal, with the facts of the proof as
premises. The answer goes on the `false:` or `refutation:` line, and in the JSON report it is a
`kind` with one of seven values. They are kept apart, because only the first two say the goal is
false:

| kind | what it means |
|---|---|
| `found` | a sampled point where the facts hold and the goal fails: the goal is false |
| `solved` | an exact point, found by solving the linear facts with the goal denied: the goal is false |
| `contradictory` | the facts of the proof cannot all hold, so every goal follows from them |
| `no-counterexample` | the linear question was decided, and nothing refutes the goal |
| `survived` | no sampled point refuted it, which is evidence and not a decision |
| `never-asked` | no point could be evaluated: a constant the model does not interpret, or a quantifier over the reals |
| `undecided` | sampling cannot settle a question of this shape |

A goal that `survived` may be true and out of reach of the method named, or false somewhere the
sampling did not look. The report says which of the seven it is and claims nothing more.

### The price of a proved theorem

A proved theorem is printed with what it asks a reader to believe and what it was built from:

```
line 38: theorem ZERO_LEFT: proved
  |- !n:num. 0 + n = n
  axioms: INFINITY, SELECT
  library facts: NUM_ADD_SUC, NUM_ADD_ZERO, NUM_INDUCTION, NUM_ZERO_ADD
  inferences: 406
```

- `axioms` is every axiom the derivation reaches, all the way down, by name.
- `library facts` is the lemmas of the library the proof cites. The walk stops at each named fact,
  so the construction of `num` under `NUM_ADD_ZERO` is not listed again.
- `from this document` names the document's own theorems the proof cites, when there are any.
- `imported` names the theorems of imported documents the proof cites, as `DOCUMENT.NAME`.
- `inferences` is the size of the derivation in kernel inferences.
- `note` appears when a bound, not the claim, decided part of the price. This is the case
  `Prove` reports as cut short.

`--json` prints the same report as one JSON object per file, for a program driving the checker.
The exit status is 0 when everything is proved or defined, nothing failed to read and every
import resolved to a document that checks, and 1 otherwise.

**One failure does not stop the checking.** A syntax error ends the declaration it is in, and the
next declaration is read. A step that fails is reported, and the rest of the proof is still
checked. A failed `have` stays in the context as an assumption, so the steps after it are checked
against the fact they were written to use. A declaration with any problem is not a fact of the
document. A later proof that cites it is told that its proof failed, not that the name does not
exist.

## Lines, blocks and comments

- One step is one line. Indentation is free and is there for the reader.
- A proof is `proof` on its own line, then the steps, then `qed`. A claim settled by one method
  can be written on one line instead: `theorem NAME : CLAIM by METHOD`.
- A step that splits the goal is followed by its branches. Each branch is `case LABEL names:`
  followed by its steps, and the group ends with `end`.
- `--` starts a comment that runs to the end of the line, when it opens the line or follows a
  space.

Blocks are closed by keywords and never by indentation. An indentation slip that reparses as a
different proof is a mistake the reader cannot see, and `docs/adr/0070` records why that decided
it.

## Declarations

| declaration | what it does |
|---|---|
| `import NAME` | The definitions and theorems of the document `NAME` can be used here. Imports come before every other declaration. |
| `define NAME := TERM` | A conservative definition. It costs a name and no belief, and `NAME` is then a fact: the defining equation. |
| `theorem NAME : CLAIM` | A claim and its proof. Once proved, `NAME` is a fact for every later declaration. |

A name is a fact once declared, so a declaration may not take the name of a lemma of the library
or of a theorem of an imported document: a later proof citing the name would reach the declaration
and not the lemma its reader knows. The checker refuses it and says which one it would hide.

```sym
define twice := \x:real. x + x

theorem TWICE : !x:real. twice x = 2 * x
proof
  fix x
  rewrite twice
  by ring
qed
```

## Steps

| step | the goal it wants | what follows |
|---|---|---|
| `fix x y` | `!x y. P` | `P`, about fixed `x` and `y` |
| `assume h k` | `A ==> B ==> C` | `C`, with `h : A` and `k : B` |
| `have h : P by M` | any | the same goal, with `h : P` |
| `have h : P` and a `proof ... qed` block | any | the same, with `P` proved by the block |
| `show P by M` | `P` | closed |
| `by M` | any | closed |
| `obtain x h from F` | any, with `F : ?x. P x` | the same goal, with a fixed `x` and `h : P x` |
| `cases h : P` | any | branches `pos` with `h : P` and `neg` with `h : ~P` |
| `cases h from F` | any, with `F : A \/ B` | branches `left` with `h : A` and `right` with `h : B` |
| `induction x` | any, with `x` fixed | one branch per case of the principle |
| `induction x using L` | the same | the cases of `L`, numbered from 1 |
| `split` | `A /\ B` | branches `left` and `right` |
| `left`, `right` | `A \/ B` | `A`, or `B` |
| `witness t` | `?x. P x` | `P t` |
| `rewrite F, G` | any | the goal rewritten with the equations named |
| `apply L` | an instance of what `L` concludes | what `L` assumes: one goal, or branches numbered from 1 |
| `calc a = b by M`, then `_ = c by M` lines | `a = c`, or an order | closed |

The names in a branch header are introduced in order: a universal is fixed under the name, and an
implication is assumed under it. `case succ m ih:` fixes `m` and assumes the induction hypothesis
as `ih`. A header with more names than its case binds is refused.

**Induction** is over a variable the proof has fixed. Over `num` the principle is `NUM_INDUCTION`
and its cases are `zero` and `succ` (or `1` and `2`). Any other principle is named with `using`,
and its cases are numbered. A fact of the proof that mentions the variable is refused, because the
induction would leave it behind; state it as a hypothesis of the claim before `fix`, so the
induction carries it.

```sym
theorem STRONG : !n:num. 0 <= n
proof
  fix n
  induction n using NUM_STRONG_INDUCTION
  case 1 k hk:
    by arith
  end
qed
```

**`calc`** chains relations. Equations compose by transitivity. A chain with an order in it is
composed by the procedure for its type, `LINARITH` over the reals and `arith` over the naturals,
and the stricter relation wins.

```sym
theorem CHAIN : !x:real. !y:real. 0 <= x /\ x <= y ==> x <= y + y
proof
  fix x y
  assume h
  calc x <= y by linarith from h
       _ <= y + y by linarith from h
qed
```

Existentials go in with `witness` and come out with `obtain`:

```sym
theorem OBTAIN : (?n:num. n + 1 = 1) ==> (?m:num. m = 0)
proof
  assume e
  obtain k hk from e
  witness k
  by arith from hk
qed
```

A classical case split, and `left` and `right`:

```sym
theorem EXCLUDED : !p:bool. p \/ ~p
proof
  fix p
  cases h : p
  case pos:
    left
    by exact h
  case neg:
    right
    by exact h
  end
qed
```

## Methods

| method | what settles the goal |
|---|---|
| `auto` | the tactic surface, `Prove`: the library lookup, `RING`, `LINARITH`, `Field`'s price, the propositional procedures and the chaining search |
| `auto from F, G` | the same, with the facts named as hypotheses |
| `ring` | `RING`, for equations of commutative rings |
| `linarith`, `linarith from F, G` | `LINARITH` over the reals, with the facts named |
| `arith`, `arith from F, G` | linear arithmetic over the naturals, with the facts named |
| `rewrite F, G` | the equations named, until the goal is `T` or `t = t`. A rewrite whose walk ran out of steps, or grew the term past the ceiling, is refused naming which, and is never read as a normal form |
| `rewrite F then M` | the equations, then `M` on what is left |
| `exact F` | the fact, or an instance of it |
| `apply L` | `L`, when it owes nothing more at this goal |
| `first M \| N` | the first of them that settles the goal, and every refusal if none does |

A name in `from`, `rewrite`, `exact` or `apply` is looked up in the proof first, then among the
document's own theorems and definitions, then in the library (`docs/lemmas.md`). `find` in the
notebook searches the library by name and by shape.

What a method returns is checked and never trusted: its conclusion must be the goal as written, and
it may rest only on hypotheses the proof holds.

## Importing another document

`docs/adr/0073` is the decision this section and the next describe. A document sees exactly what
it imports, directly or through another import: their definitions,
made again in the theory it is read in, and their theorems, which it cites by name. A document it
does not import is invisible to it, even one checked earlier, so what a document rests on is what
its imports say.

```sym Doubling
define DOUBLE := \n:num. n + n

theorem DOUBLE_ZERO : DOUBLE 0 = 0
proof
  rewrite DOUBLE
  by arith
qed

theorem DOUBLE_SUC : !n:num. DOUBLE (SUC n) = SUC (SUC (DOUBLE n))
proof
  fix n
  rewrite DOUBLE
  by arith
qed
```

```sym Parity
import Doubling

theorem EVEN_OR_ODD : !n:num. ?k:num. n = DOUBLE k \/ n = SUC (DOUBLE k)
proof
  fix n
  induction n
  case zero:
    witness 0
    left
    by rewrite DOUBLE_ZERO
  case succ m ih:
    obtain k hk from ih
    cases h from hk
    case left:
      witness k
      right
      by rewrite h
    case right:
      witness SUC k
      left
      calc SUC m = SUC (SUC (DOUBLE k)) by rewrite h
           _ = DOUBLE (SUC k) by rewrite DOUBLE_SUC
    end
  end
qed
```

The price of `EVEN_OR_ODD` lists `imported: Doubling.DOUBLE, Doubling.DOUBLE_SUC, Doubling.DOUBLE_ZERO`.

An import that cannot be used is a problem of the importing document, on the import line: a name
with no document, a document importing itself, two documents importing each other, or two imported
documents declaring one name. An imported document that does not check is reported the same way,
and what it did prove is still imported, so the importer's proofs are checked against the facts
they were written to use. A proof citing one of its failed declarations is told the proof failed,
with the document and the line.

## Publishing a document

A document under `modules/published/src/main/resources/garden/xeno/symbolum/published/`, named in
`Published.Names`, is published. Every run of the suite checks it, its theorems are a library
(`Published.standard.library`) beside the chain's, and [published.md](published.md) lists them and
is regenerated with

```
tools/sbt "published/runMain garden.xeno.symbolum.published.Published"
```

Publishing refuses three things a single check cannot see:

- a published document that does not check, in any declaration or import;
- a name two published documents both declare, even when neither imports the other: every
  published document is made again in one theory, where the kernel refuses a name defined twice;
- an axiom. The language has no declaration that asserts one, and the published theory is compared
  with the chain's.

## In the notebook

The notebook (`tools/sbt "published/runMain garden.xeno.symbolum.published.Notebook"`) takes the
language a declaration at a time. A cell that starts with `theorem` is that theorem, and with
`proof` on the line after it, the cell runs to the `qed` that closes the proof. The checker's
elaborator checks it against the session as it stands: the constants the session declared and
defined read in the claim, and a proof may cite what the session holds by name, an assumption
included. A proved theorem joins the session with its price, where `from this session` names the
facts of the session it cited. A proof that does not check is shown as the checker shows it, every
problem with the goal at that point, and the session gains nothing from it.

```
declare p : bool
assume P : p
theorem Q : p by exact P
theorem ZERO_RIGHT : !n:num. n + 0 = n
proof
  fix n
  show n + 0 = n by arith
qed
```

Pasted whole, that is four cells. `show` inside the proof is the proof's step, because the cell
ends at `qed` and not at the next line that looks like a command. In the box, Enter runs a cell and
Shift+Enter starts a new line.

`import NAME` takes a published document into the session: its definitions are made in the
session's theory, its theorems become facts, and the same happens for every document it imports.
It is all of that or nothing. A document that does not check, a definition the session already
made differently, or a theorem whose name the session already holds leaves the session as it was.
`import` is a cell of its own, and inside a `theorem` cell it is refused. `docs/adr/0074` is the
decision.

## What it does not do yet

`docs/adr/0070` plans the work in six increments. This file describes the first three and the
fifth, which came before the fourth. Until the others land:

- a published theorem is reached by importing its document; `auto`, `find` and `Ask` search the
  chain's library and not the published one;
- the goal is shown in the report and in the notebook, and not yet in an editor;
- there is no `simp` set and no `datatype` declaration.
