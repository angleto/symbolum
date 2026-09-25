#!/bin/sh
# Fire the guards of cards eb258a45 (a decided higher-order variable is checked where it recurs)
# and 2efed305 (`Matching.why` spent outside its spec, as `BeyondMatching`) at the defects they are for.
#
# Written by the verification of both cards on 2026-09-25 against `87175842`, from the perturbation
# plans their delivering comments wrote down and nobody had run as a file. Each perturbation takes
# one repair away; the expectation beside it is what the delivering comment predicted, and the log
# is where the answer is read.
#
# A drops the termination guard of `Matching.decided`: a decided term that mentions a pattern
# variable goes back to the walk. Expect `MatchingSpec` to die with `StackOverflowError` on
# "stop where the decided term mentions the pattern's own variable".
# B sends a decided head back to what it was before 2026-09-25, a refusal. Expect red on "be checked
# where it recurs", "solve a variable still unsolved", "decide the types too", the nested case
# "turn the pattern into the target where the decided variable recurs inside its own argument",
# and `LogicSpec`'s "specialise a principle whose predicate recurs applied to a non-binder".
# C opens the pattern side of a binder in `Matching.firstRefusal` at the target's variable, which
# is what it did before 2026-09-25. Expect red on "name the condition under a binder over a type
# variable".
# D takes `Matching.why` out of `Rules.unmatched`, so a refusal at the fragment's boundary says
# again that the target is no instance. Expect red on `LogicSpec`'s "say the fragment was left".
#
# The strings are literal and were unique when this was written; C carries the line before it,
# because the same `open(pattern, inPattern)` occurs first in `matchTerm`. perturb.sh REFUSES a
# perturbation that did not apply rather than running against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/decided-variable.log"
MATCHING=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Matching.scala
RULES=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rules.scala
SPECS='logic/testOnly garden.xeno.symbolum.logic.MatchingSpec garden.xeno.symbolum.logic.LogicSpec'
NL='
'

GUARDED='if (solvable.isEmpty && !Term.freeVariables(value).exists(variables.contains))'
UNGUARDED='if (solvable.isEmpty)'
DECIDED='decided(acc.terms(variable), arguments, target, binders, acc)'
REFUSED='None'
OPENED="(for {${NL}            patternBody <- open(pattern, inPattern)"
MISOPENED="(for {${NL}            patternBody <- open(pattern, inTarget)"
BEYOND='case Some(refusal) => BeyondMatching(body, target, refusal)'
NOT_OF_FORM='case Some(_) => NotOfForm(s"an instance of $body", target)'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
run "0-control" ./tools/sbt -batch "$SPECS"
run "A-no-termination-guard" "$P" "$MATCHING" "$GUARDED" "$UNGUARDED" -- ./tools/sbt -batch "$SPECS"
run "B-decided-refused" "$P" "$MATCHING" "$DECIDED" "$REFUSED" -- ./tools/sbt -batch "$SPECS"
run "C-why-opens-at-the-target" "$P" "$MATCHING" "$OPENED" "$MISOPENED" -- ./tools/sbt -batch "$SPECS"
run "D-unmatched-without-why" "$P" "$RULES" "$BEYOND" "$NOT_OF_FORM" -- ./tools/sbt -batch "$SPECS"

echo "### all fired" >> "$LOG"
git status --porcelain >> "$LOG"
