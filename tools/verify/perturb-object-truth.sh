#!/bin/sh
# Fire the two claims TruthSpec makes about the truth of the object language, card 4102f131.
#
# Every clause of `NUM_TRUE` is compared with its published statement, so a perturbation of the
# step alone is caught at the construction and says nothing about the spec's other tests. What
# these perturbations change is the step AND the statement together, which is the defect a clause
# comparison cannot see: a truth predicate that is wrong and says so consistently.
#
# 1. The quantifier reads its body at `e` unchanged rather than at `e` updated at the bound index.
#    Expected: red at "read its body at the updated environment", which evaluates
#    `~ !v0. v0 = 0` at the environment sending everything to zero; unchanged, the body reads
#    `0 = 0` and the evaluation no longer reaches `~(!n. n = ZERO)`.
# 2. The negation's clause drops the negation. Expected: red at the same test, and at the
#    refutation of `0 = S 0` nowhere, since that formula has no negation in it; the pair is what
#    says the quantifier test is not red for a reason unrelated to its subject.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN is recorded under the run, on the tree that landed this.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/object-truth.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-the-update-forgotten" >> "$LOG"
"$P" "$TRUTH" \
  '"                          (\\k:num. COND (k = NUM_FST (NUM_PAYLOAD s)) n (e k))) " +' \
  '"                          (\\k:num. e k)) " +' \
  -- "$P" "$TRUTH" \
  '"(!n:num. NUM_TRUE p (\\k:num. COND (k = j) n (e k)))"),' \
  '"(!n:num. NUM_TRUE p (\\k:num. e k))"),' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-update-forgotten" >> "$LOG"

echo "################ 2-the-negation-dropped" >> "$LOG"
"$P" "$TRUTH" \
  '"           (\\e:num -> num. ~(f (NUM_PAYLOAD s) e)) " +' \
  '"           (\\e:num -> num. f (NUM_PAYLOAD s) e) " +' \
  -- "$P" "$TRUTH" \
  'NUM_TRUE (NUM_CODE 6 p) e = ~(NUM_TRUE p e)' \
  'NUM_TRUE (NUM_CODE 6 p) e = NUM_TRUE p e' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-negation-dropped" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
