#!/bin/sh
# Fire DatatypeSpec at two defects of the builder it exists to catch, card 9b02e0ba.
#
# Both are defects that produce a type and its facts rather than a refusal, which is why they are
# the ones worth firing: a builder that refused would be caught by any use of it, and a builder
# that proved the wrong theorem is caught only by something that compares the theorem with what
# it should have been.
#
#   1. The fixed arguments read from the wrong slot of the label. A constructor with three fixed
#      arguments of two types still yields an injectivity, and it equates the first argument
#      three times; `item`'s statement comparison is what reads it.
#   2. The recursion's result type allowed to collide with a parameter of the type. `btree('a,'b)`
#      then recurses into `'b`, which is a theorem about functions into the tree's own second
#      parameter and a weaker one; the comparison with `'b1` is what reads it.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, on the tree that landed this. Control green at 12 tests, both red,
# restore verified clean by the tool.
#
#   1. Red at 9 of 12, and NOT for the reason this header predicted. No wrong theorem came out: the
#      derivation refused, `application: expected b, found a` at `btree` and `expected bool, found
#      num` at `item`, because an argument read from another slot has another slot's type and the
#      injectivity cannot be assembled. So the statement comparison is not what caught it; the
#      builder's own typing did, and the three that stayed green are the refusals, which build no
#      type. A slot mix-up between two slots of ONE type would not refuse, and `item`'s first and
#      third slots are that pair: they are both `num`, and this perturbation moves both to the
#      first, which the typing of the second slot stopped before the comparison could read it.
#   2. Red at 1 of 12, the recursion's statement, printed with `'b` where `'b1` was expected: the
#      builder proved a theorem about functions into the tree's own second parameter, and only the
#      comparison with the written statement said so.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Datatype.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.DatatypeSpec'

echo "################ 0-control" >> "$OUT/datatype.log"
./tools/sbt -batch "$SPEC" >> "$OUT/datatype.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/datatype.log"

echo "################ 1-every-argument-from-the-first-slot" >> "$OUT/datatype.log"
"$P" "$SOURCE" \
  'result = owned.map(slot => components(1 + slot))' \
  'result = owned.map(slot => components(1 + owned.head))' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/datatype.log" 2>&1
echo "### exit $? for 1-every-argument-from-the-first-slot" >> "$OUT/datatype.log"

echo "################ 2-a-result-type-that-collides" >> "$OUT/datatype.log"
"$P" "$SOURCE" \
  '.find(!used.contains(_)).get' \
  '.find(_ => true).get' \
  -- ./tools/sbt -batch "$SPEC" >> "$OUT/datatype.log" 2>&1
echo "### exit $? for 2-a-result-type-that-collides" >> "$OUT/datatype.log"
