#!/bin/sh
# Measure, for card 4102f131's increment `NUM_VALUE_SUBST_NUMERAL` and `NUM_TRUE_SUBST_NUMERAL`,
# that what the formula lemma stands on is load-bearing rather than beside it.
#
# 1. Under a universal over an index other than `x`, the two updates of the environment commute
#    only after the inner `COND (m = x) k (e m)` is reduced to `e m` under the outer conditional.
#    With that congruence replaced by the bare reduction, the two sides of the point no longer
#    meet and the chain should refuse to build.
# 2. The environments are equated by the kernel's abstraction rule over their bodies and not by
#    extensionality, because extensionality is reached through `ETA` and every fact of `Truth`
#    costs choice and infinity alone. With extensionality put back, the chain builds and
#    `TruthSpec`'s per-fact cost should go red naming `NUM_TRUE_SUBST_NUMERAL` with `ETA`.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-21, on the tree that became the commit carrying this file: the control
# green at 11 of 11, the tree restored after each perturbation, and both as predicted.
# 1. All 11 red, every one at `Chain.standard`: "transitivity: (((COND (m = u)) n) (e m)) is not
#    (e m)", the outer conditional left around the point where the bare reduction was offered.
# 2. 10 of 11 green and the cost test red, its report reading "NUM_TRUE_SUBST_NUMERAL: ETA,
#    INFINITY, SELECT" against choice and infinity alone. The chain builds, so the abstraction is
#    what keeps the fact off eta, and the cost test is the only thing that says so.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TRUTH=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Truth.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.TruthSpec'
LOG="$OUT/true-at-numeral.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

echo "################ 1-without-the-congruence-under-the-conditional" >> "$LOG"
"$P" "$TRUTH" '                      same(passed(notXm, k, cond(equal(m, u), n, em)), rightSide)' \
  '                      same(passed(notXm, k, cond(equal(m, u), n, em)), inner)' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-without-the-congruence-under-the-conditional" >> "$LOG"

echo "################ 2-extensionality-instead-of-abstraction" >> "$LOG"
"$P" "$TRUTH" '        val joined = force(LogicError.lift(Kernel.abs(m, point)))' \
  '        val joined = force(Conv.betaRoot(applied(f, List(m))).flatMap(atM => Conv.betaRoot(applied(h, List(m))).flatMap(atN => Conv.sym(atN).flatMap(back => Conv.trans(atM, point).flatMap(Conv.trans(_, back))))).flatMap(rules.gen(m, _)).flatMap(g.classical.ext(logic, _)))' -- \
  ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-extensionality-instead-of-abstraction" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
