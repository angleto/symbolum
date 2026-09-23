#!/bin/sh
# Fire the three claims the structural recursion and its consumer make about themselves, card
# 708faa52.
#
# All three are claims about a DERIVATION and not about a statement, so nothing printed carries
# them and no assertion over `Listing.Statements` or `Folding.Statements` can fail for one. What
# can is the construction refusing when the step that carries the weight is taken away, and
# because both developments are built once inside `Chain.construct`, a refusal here is red at the
# chain and every spec in the module aborts with it.
#
# 1. The recursion's step reads the head and the TAIL of the cons it is applied to, and the tail
#    twice: once as `g`'s second argument and once as the argument of the recursive call. The
#    second is the one that makes the recursion descend at all -- without it the call is at a term
#    nothing has related to `w` -- and it is invisible in the statement, which says only that some
#    function exists.
# 2. `Listing.structuralRecursion` and `Folding.foldOverAConcatenation` choose their bound variable
#    fresh against what the STATEMENT BINDS and not against what is free in it. The statements are
#    closed, so what is free in them is empty; this is the defect that actually happened while the
#    file was being written, and the perturbation is the two-character edit that puts it back.
# 3. The fold's step discards the tail, which `docs/adr/0039` says is what makes `LIST_FOLD_CONCAT`
#    provable rather than a convenience. The perturbation cannot hand the tail back -- `g`'s type
#    forbids it -- so what it does instead is take away the one step in the split that turns
#    `WORD_CONCAT (LIST_CONS x u) v` into `LIST_CONS x (WORD_CONCAT u v)`, which is where the two
#    tails would differ if they could.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-23, on the tree that landed this. Control green at 16 tests; all three
# red at the chain; restore verified clean by `git status --porcelain` at the end.
#
# **Two of the three refusals were predicted wrong before the run, and the prediction is left
# corrected here rather than quietly replaced.** Both 1 and 3 were expected to fail the comparison
# against the statement -- `expected the value at a cons as it is written` -- and both fail
# EARLIER, inside `Conv.trans`, because the chain of equations stops at the step the perturbation
# removed and never reaches the comparison at all. The comparison against the statement is the
# last line of defence and not the first, which is a better answer than the one predicted.
#
#   1. `transitivity: (y (LIST_HEAD (LIST_CONS x y1)) (LIST_TAIL (LIST_CONS x y1))
#      (F (WORD_LENGTH y1) (LIST_CONS x y1))) is not (... (F (WORD_LENGTH y1)
#      (LIST_TAIL (LIST_CONS x y1))))`. The two terms printed side by side differ in exactly one
#      place, the argument of the recursive call, which is the whole content of the perturbation.
#   2. `expected the split at the empty left half, found LIST_FOLD x y (WORD_CONCAT WORD_EMPTY u)
#      = LIST_FOLD x (LIST_FOLD x y u) WORD_EMPTY`. The capture, printed: what the induction asks
#      for has `WORD_EMPTY` where the statement's own `v` stands, because the abstraction took a
#      variable the statement had already bound. This is the one of the three whose message was
#      predicted right, and it is the one that had actually happened.
#   3. `transitivity: LIST_FOLD x y (WORD_CONCAT u1 u) is not LIST_FOLD x y (LIST_CONS x1
#      (WORD_CONCAT y1 u))`. Without the move there is no cons for `LIST_FOLD_CONS` to fire on, so
#      what the step reached and what the next equation is about do not meet.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LISTING=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Listing.scala
FOLDING=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Folding.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ListingSpec garden.xeno.symbolum.theories.FoldingSpec'
LOG="$OUT/list-structural-recursion.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. The recursive call taken at the subject rather than at its tail. `F n (LIST_TAIL w)` is what
# makes the auxiliary function descend; `F n w` is well-typed, builds a perfectly good function,
# and is not the one the statement asks for. Nothing about the types catches it.
echo "################ 1-the-call-not-at-the-tail" >> "$LOG"
"$P" "$LISTING" \
  'recursiveCall <- LogicError.lift(Term.app(previous, tailOfSubject))' \
  'recursiveCall <- LogicError.lift(Term.app(previous, subject))' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-call-not-at-the-tail" >> "$LOG"

# 2. The fresh variable chosen against what is free in the statement rather than against what it
# binds. The statement is closed, so the first set is empty and the second is not: this is the
# defect that happened while the file was written, and the comment beside the line records it.
echo "################ 2-fresh-against-the-free-set" >> "$LOG"
"$P" "$FOLDING" \
  'taken = Term.freeVariables(goal) ++ variables.toSet' \
  'taken = Term.freeVariables(goal)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-fresh-against-the-free-set" >> "$LOG"

# 3. The step's one move taken away: without `WORD_CONCAT (LIST_CONS x u) v = LIST_CONS x
# (WORD_CONCAT u v)` there is no cons for `LIST_FOLD_CONS` to fire on, and the induction's step
# does not start. It is the whole content of the split and it is not visible in the statement.
echo "################ 3-the-cons-not-moved-out" >> "$LOG"
"$P" "$FOLDING" \
  'carried <- Conv.apTerm(outer, moved)' \
  'carried <- Right(Conv.refl(onTheLeft))' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-cons-not-moved-out" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
