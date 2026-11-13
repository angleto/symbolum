#!/bin/sh
# Fire the guard of card 4102f131's increment that makes the object logic instantiate at any
# substitutable term (docs/adr/0078): the capture test in `LanguageSpec`.
#
# The defect it is for is a definition of `NUM_FREE_FOR` whose quantifier clause forgets the
# binder, which would let specialisation put `v_1` under `!v_1.` and derive a falsity in PA. The
# perturbation writes exactly that definition, consistently: the step, the published statement,
# the one line of the closedness proof that used the dropped conjunct, and the one line of
# `Deduction` that builds the conjunct for a quantifier whose binder is another index, so that the
# chain still builds and what goes red is the attack rather than a proof that stopped composing.
# The `Deduction` line was missing from the first version, and that run aborted the suite with
# "the standard chain does not build": a red, and not the one this harness is for.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-12 over d47d4901: control 38 of 38; perturbed, the capture test alone red
# and 37 green. `docs/adr/0078` carries it under what was measured.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

FILE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Language.scala
CONSUMER=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Deduction.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.LanguageSpec'
LOG="$OUT/substitutable.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-binder-forgotten" >> "$LOG"
"$P" "$FILE" '"                              ~(NUM_FREE_TERM (NUM_FST (NUM_PAYLOAD s)) t) /\\ " +' \
  '"                              " +' -- \
  "$P" "$FILE" '~(NUM_FREE_TERM j t) /\\ NUM_FREE_FOR i t p)"' 'NUM_FREE_FOR i t p)"' -- \
  "$P" "$FILE" 'both <- rules.conjIntro(binderAbsent, body)' \
  'both <- rules.conjIntro(binderAbsent, body).map(_ => body)' -- \
  "$P" "$CONSUMER" 'rules.conjIntro(boundAbsent, bodyAccepts).flatMap(rules.disjIntro2(notFreeInBody, _)))' \
  'Right(bodyAccepts).flatMap(rules.disjIntro2(notFreeInBody, _)))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-binder-forgotten" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
