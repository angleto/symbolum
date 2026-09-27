#!/bin/sh
# Fire the reals as cuts at the choices their central arguments make, cards 709a37d4, c71986c3 and c72f04ee.
#
# 1. The least upper bound is the union of the family's members, `\q. ?x. P x /\ dest_cut x q`.
#    Dropping `P x` makes it the union of every cut, which holds every rational and is not a cut, so
#    the construction must refuse at `CUT_COMPLETE`: this is what says the family is read at all.
# 2. `CUT_OF_RAT q` is the rationals strictly below `q`. Below or equal has a greatest element, `q`,
#    so it is not a cut, and the construction must refuse where the embedding's members are read
#    back through the characterisation.
# 3. `CUT_ESCAPE`, which both inverses spend, walks `e + n * f` through the cut by induction and
#    looks for a member whose step `p + f` leaves it. Since 2026-09-26 the step lives there rather
#    than inside the additive inverse. Stepping by nothing reaches `e + n * f + 0` at the induction
#    step, which the ring does not identify with `e + (n + 1) * f`, so the induction refuses.
# 4. The multiplicative inverse steps by `h = p0 (1 - l) / l`, which is what makes `l * s <= p` for
#    the escaping member. Dropping the division by `l` breaks that one inequality, and the ring's
#    consequence refuses it.
# 5. `CUT_MUL` negates the core in the mixed-sign branches. Leaving one un-negated gives a product
#    that is not commutative across signs, and the commutativity derivation refuses.
#
# CutSpec is the spec: every fact is derived inside `Cut.construct`, so a refusal aborts the suite at
# construction, which is the red this expects. The control before must be green. Each target was
# counted before the first run and occurs once in `Cut.scala`.
#
# WHAT WAS SEEN, 2026-09-26, with the product and the inverse: control green at 12 tests, all five
# perturbed runs aborted construction, restore verified after each. 1 and 2 as recorded below. 3
# refused at the induction step of `CUT_ESCAPE`, the ring finding `e + f * n` against
# `e + (f + f * n)`, as predicted. 5 refused at commutativity, `CUT_PMUL x (-y)` against its
# negation, as predicted. 4 did NOT refuse where predicted: not at `l * s <= p` but earlier, where the
# proof of `0 < h` is handed to `CUT_ESCAPE`, because that proof still builds the divided step. So 4
# shows that the step and its positivity are one term; the inequality's need for the division is not
# reached by any perturbation here.
#
# WHAT WAS SEEN, 2026-09-25: control green at 9 tests; all three perturbed runs aborted construction.
# 2 and 3 refused where predicted: the characterisation refused `IS_CUT (\p. RAT_LE p q)` against a
# witness for `RAT_LT`, and the ring refused `p` against `f + p`. 1 did NOT refuse where predicted.
# The prediction was that the union of every cut is refused for not being a cut; what refused was
# the first clause of the derivation, which still reads the family through `P x` and found the union
# without it. So 1 shows that the union and every use of it are one text and not two, which is
# worth having, and does not show the not-a-cut refusal, which no perturbation here reaches yet.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Cut.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.CutSpec'
LOG="$OUT/cuts.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# The binder read `?x:cut.` until `docs/adr/0053` named the type `real`; repaired in that change.
echo "################ 1-the-union-of-every-cut" >> "$LOG"
"$P" "$SOURCE" \
  'read("\\q:rat. ?x:real. P x /\\ dest_cut x q", setType)' \
  'read("\\q:rat. ?x:real. dest_cut x q", setType)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-the-union-of-every-cut" >> "$LOG"

echo "################ 2-the-embedding-at-most" >> "$LOG"
"$P" "$SOURCE" \
  'mk_cut (\\p:rat. RAT_LT p q)' \
  'mk_cut (\\p:rat. RAT_LE p q)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 2-the-embedding-at-most" >> "$LOG"

echo "################ 3-the-step-by-nothing" >> "$LOG"
"$P" "$SOURCE" \
  'stepped <- plus(p, f)' \
  'stepped <- plus(p, zero)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 3-the-step-by-nothing" >> "$LOG"

echo "################ 4-the-inverse-step-undivided" >> "$LOG"
"$P" "$SOURCE" \
  'h <- times(p0om, il)' \
  'h <- times(p0om, oneTerm)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 4-the-inverse-step-undivided" >> "$LOG"

echo "################ 5-a-mixed-sign-branch-unnegated" >> "$LOG"
"$P" "$SOURCE" \
  '"(COND (CUT_LE (CUT_OF_RAT RAT_ZERO) y) (CUT_PMUL x y) (CUT_NEG (CUT_PMUL x (CUT_NEG y)))) " +' \
  '"(COND (CUT_LE (CUT_OF_RAT RAT_ZERO) y) (CUT_PMUL x y) (CUT_PMUL x (CUT_NEG y))) " +' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 5-a-mixed-sign-branch-unnegated" >> "$LOG"
