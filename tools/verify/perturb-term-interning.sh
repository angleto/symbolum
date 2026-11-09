#!/bin/sh
# Fire the guards of one instance per term, card 580c80ef and `docs/adr/0069`, at the two defects
# they were written for: a table that hands back the candidate, and a `fromProduct` that builds.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-11-09, on the tree that landed this. Control green (TermInterningSpec and
# TermPropertySpec 17, TrustBoundarySpec 9); every perturbation red where named, restores verified.
#
#   1. `false was not equal to true` on the four identity tests and the kept-hash property; the
#      refusal stayed green.
#   2a. `should be refused, since nothing checks it there *** FAILED ***`.
#   2b. `should not come out of a case class's mirror ... *** FAILED ***`.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TERM_SCALA=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Term.scala
KERNEL='kernel/testOnly garden.xeno.symbolum.kernel.TermInterningSpec garden.xeno.symbolum.kernel.TermPropertySpec'
BOUNDARY='logic/testOnly garden.xeno.symbolum.logic.TrustBoundarySpec'

echo "################ 0-control" >> "$OUT/interning.log"
./tools/sbt -batch "$KERNEL" "$BOUNDARY" >> "$OUT/interning.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/interning.log"

# 1. No table: every construction is a new object, as before the change. Expect red on every
# identity assertion of `TermInterningSpec` but the refusals, and on the kept hash's in
# `TermPropertySpec`, whose `eq` is what carries the property since the change.
echo "################ 1-no-table" >> "$OUT/interning.log"
"$P" "$TERM_SCALA" \
  '      case None => candidate' \
  '      case None => candidate
      case Some(_) if candidate ne null => candidate' \
  -- ./tools/sbt -batch "$KERNEL" >> "$OUT/interning.log" 2>&1
echo "### exit $? for 1-no-table" >> "$OUT/interning.log"

# 2. The mirror builds again: `App.fromProduct` constructs, unchecked, which is the route measured
# open before the change. Run twice, because sbt stops at the first red command and the second
# would otherwise never be asked. Expect red on the refusal in `TermInterningSpec` (2a) and in
# `TrustBoundarySpec`, which asks from outside the package (2b).
MIRROR_FROM='def fromProduct(product: Product): App = interned.refuse(product)'
MIRROR_TO='def fromProduct(product: Product): App = product.productIterator.toList match {
    case List(fn: Term, arg: Term) => apply(fn, arg)
    case _ => interned.refuse(product)
  }'
for run in "2a-mirror-builds-inside:$KERNEL" "2b-mirror-builds-outside:$BOUNDARY"; do
  name=${run%%:*}; command=${run#*:}
  echo "################ $name" >> "$OUT/interning.log"
  "$P" "$TERM_SCALA" "$MIRROR_FROM" "$MIRROR_TO" \
    -- ./tools/sbt -batch "$command" >> "$OUT/interning.log" 2>&1
  echo "### exit $? for $name" >> "$OUT/interning.log"
done

cd "$WT" && git status --porcelain >> "$OUT/interning.log"
