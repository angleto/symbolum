#!/bin/sh
# Re-fire the four guards of card cfc581a3 at the defects they were written for.
# Run in the measurement worktree so the shared checkout is never edited.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SESSION=modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Session.scala
SPEC=modules/tactics/src/test/scala/garden/xeno/symbolum/tactics/SessionSpec.scala

run() { # name, then perturb.sh args
  n="$1"; shift
  echo "################ $n" >> "$OUT/perturb.log"
  "$P" "$@" >> "$OUT/perturb.log" 2>&1
  echo "### exit $? for $n" >> "$OUT/perturb.log"
}

# 0. THE CONTROL. A red under a perturbation proves nothing unless the same command is green
# without it: perturb.sh refuses a perturbation that did not apply, and says itself that it does
# not decide whether a failure is the RIGHT failure.
echo "################ 0-control" >> "$OUT/perturb.log"
./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.SessionSpec garden.xeno.symbolum.tactics.DocumentationSpec' >> "$OUT/perturb.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/perturb.log"

# 1. the fold put back to running every step from `start`
run "1-fold-unthreaded" "$SPEC" \
  'val next = session.run(step)' 'val next = start.run(step)' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.SessionSpec'

# 2. the session holding no fact at all
run "2-no-fact" "$SESSION" \
  'named.reverse.collectFirst { case (held, theorem) if held == name => theorem }' 'None' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.SessionSpec'

# 3. `derive` taken out of the document, code untouched
run "3-doc-drops-derive" AGENTS.md \
  '`prove`, `derive`, `ask`' '`prove`, `ask`' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.DocumentationSpec'

# 4. `derive` taken out of the code, document untouched -- the other direction
run "4-code-drops-derive" "$SESSION" \
  '"prove", "derive", "ask"' '"prove", "ask"' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.DocumentationSpec'

echo "### all four fired" >> "$OUT/perturb.log"
cd "$WT" && git status --porcelain >> "$OUT/perturb.log"
