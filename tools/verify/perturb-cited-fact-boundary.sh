#!/bin/sh
# Fire the boundary at a cited fact, card 5a54c044 and `docs/adr/0047`, at the three ways it could
# stop holding while every statement stays the same.
#
# A citation changes no sequent, so no assertion over what is proved can see it. What can is a
# size: the boundary is where a report stops walking, and the measurement in `IntegerSpec` reads
# the same facts two ways, what a report reads and what a checker replays. So each perturbation
# takes one piece of the boundary away and the reading of that spec is what must go red.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, on the tree that landed this. Control green (IntegerSpec 18,
# DerivationSpec 14), all three red where named, restores verified by the tool.
#
#   1. `15374 was not less than 7687`: `INT_EQUAL` read twice what it replays, which is the whole
#      graph counted as its own, the state before the boundary.
#   2. `15388 was not less than 7696`: the same, with its nine citations still counted, which is
#      why the census alone could not have caught it.
#   3. `Set() was not equal to Set(c)`: the axiom under the citation, gone from the answer.
#   4. `published without a citation: Vector(Order.LE_OF_NOT_LT, ...`: the library half, naming
#      the development and each fact.
#   5. `a facts field that is not cited: Vector(.../Pigeonhole.scala)`: the source half, which is
#      the only one that sees a development beside the chain.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

PUBLISHED=modules/logic/src/main/scala/garden/xeno/symbolum/logic/Published.scala
DERIVATION=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Derivation.scala
INTEGERS='theories/testOnly garden.xeno.symbolum.theories.IntegerSpec'
KERNEL='kernel/testOnly garden.xeno.symbolum.kernel.DerivationSpec'

echo "################ 0-control" >> "$OUT/cited.log"
./tools/sbt -batch "$INTEGERS" "$KERNEL" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/cited.log"

# 1. Nothing cited: a development publishes its facts as they were. Every proof reads what it
# replays, which is the state before the boundary. Expect red on the carving test of
# `IntegerSpec`, at the citation count and at the ratio.
echo "################ 1-nothing-cited" >> "$OUT/cited.log"
"$P" "$PUBLISHED" \
  'case _ => name -> Kernel.cite(name, theorem)' \
  'case _ => name -> theorem' \
  -- ./tools/sbt -batch "$INTEGERS" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 1-nothing-cited" >> "$OUT/cited.log"

# 2. Cited and walked through anyway: the walk a report uses follows a citation's premise. The
# census still counts citations, so this is the one the ratio alone has to catch.
echo "################ 2-walked-through" >> "$OUT/cited.log"
"$P" "$DERIVATION" \
  'case Citation(_, _) => Nil' \
  'case Citation(_, fact) => List(fact)' \
  -- ./tools/sbt -batch "$INTEGERS" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 2-walked-through" >> "$OUT/cited.log"

# 3. The walk stops and forgets what is under it: the axioms a cited fact rests on are not added.
# Every size stays right and the accounting goes wrong, which is the failure a boundary invites.
# Expect red in `DerivationSpec`, "leave what a proof rests on exactly what it was".
echo "################ 3-axioms-left-behind" >> "$OUT/cited.log"
"$P" "$DERIVATION" \
  'case citation: Citation => found ++ citation.axioms' \
  'case citation: Citation => found' \
  -- ./tools/sbt -batch "$KERNEL" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 3-axioms-left-behind" >> "$OUT/cited.log"

# 4. A development of the chain that publishes without citing, which is how `CommutativeRing` and
# `Pigeonhole` arrived. Expect red on `LibrarySpec`'s "reach its consumers as a citation", at both
# halves: the entries of `Order` in the library, and the field in the source.
LIBRARY='theories/testOnly garden.xeno.symbolum.theories.LibrarySpec'
echo "################ 4-a-chain-link-uncited" >> "$OUT/cited.log"
"$P" modules/theories/src/main/scala/garden/xeno/symbolum/theories/Order.scala \
  'val facts: Map[String, Kernel.Thm] = Published.cite(published)' \
  'val facts: Map[String, Kernel.Thm] = published' \
  -- ./tools/sbt -batch "$LIBRARY" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 4-a-chain-link-uncited" >> "$OUT/cited.log"

# 5. The same beside the chain, where the library cannot see it. Expect red at the source half only.
echo "################ 5-beside-the-chain-uncited" >> "$OUT/cited.log"
"$P" modules/theories/src/main/scala/garden/xeno/symbolum/theories/Pigeonhole.scala \
  'val facts: Map[String, Kernel.Thm] = Published.cite(published)' \
  'val facts: Map[String, Kernel.Thm] = published' \
  -- ./tools/sbt -batch "$LIBRARY" >> "$OUT/cited.log" 2>&1
echo "### exit $? for 5-beside-the-chain-uncited" >> "$OUT/cited.log"

cd "$WT" && git status --porcelain >> "$OUT/cited.log"
