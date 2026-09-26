#!/bin/sh
# Card 0c00cac9 (and 2a48d6d0 beside it): fire the two guards its verification added, at the kept
# hash of a term and at the reach that walks through a cited fact, and the node assertion of
# 2a48d6d0 in `ReachSpec`.
#
# The card made `App` and `Abs` keep their hash, and credited that for what `Reach.of` stopped
# costing. The property it added holds the kept hash to the structural one, which a hash recomputed
# at every asking satisfies too, so nothing went red if the hash stopped being kept. The guard
# `TermPropertySpec` gained at the verification asks for the hash of a term whose sharing makes a
# recomputed hash exponential. Perturbation 1 puts `App` back to recomputing and must turn that
# guard red while the property beside it stays green.
#
# `docs/adr/0047` leaves `Reach.of` walking through every citation, by decision. The kernel's own
# case of that in `DerivationSpec` asks about a statement the root of its proof already concludes,
# so a reach that stopped at the citation would pass it. The case `RestsOnSpec` gained asks about
# the named facts inside a fact the chain publishes. Perturbation 2 makes `restingOn` walk only the
# proof's own part and must turn that case red; `DerivationSpec` staying green is the finding.
#
# The control is the run before them, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-26, on 7.0 at 1bcad72b plus the two specs. Control green (kernel 25,
# RestsOnSpec 8), all three red where named, restores verified by the tool.
#
#   1. `Future timed out after [30 seconds]` on "not walk the term when asked", and it alone: the
#      property beside it, "the same for an equal term built another way", stayed green.
#   2. `Set("COND_FALSE") did not contain all elements of List("SELECT", "COND")` on the new case,
#      and "A numeral fact should rest on the subject" red with it, since `0 < 12` reaches the
#      reals' axioms only through citations. `DerivationSpec` stayed green, all of it.
#   3. `251374 was not less than 251374`: every replayed step counted as read, which is the state
#      before the boundary.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

TERM_SCALA=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Term.scala
DERIVATION=modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Derivation.scala
KERNEL='kernel/testOnly garden.xeno.symbolum.kernel.TermPropertySpec garden.xeno.symbolum.kernel.DerivationSpec'
REACH='theories/testOnly garden.xeno.symbolum.theories.RestsOnSpec'
LOG="$OUT/kept-hash.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$KERNEL" "$REACH" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. `App` recomputes its hash at every asking, which is the state before the card. The first
# occurrence of the pair is `App`'s. Expect red on "not walk the term when asked" only.
echo "################ 1-hash-recomputed" >> "$LOG"
"$P" "$TERM_SCALA" \
  'private val hash = scala.util.hashing.MurmurHash3.productHash(this)
  override def hashCode(): Int = hash' \
  'override def hashCode(): Int = scala.util.hashing.MurmurHash3.productHash(this)' \
  -- ./tools/sbt -batch "$KERNEL" >> "$LOG" 2>&1
echo "### exit $? for 1-hash-recomputed" >> "$LOG"

# 2. The reach stops at a citation, as the accounting walks do. Expect red on `RestsOnSpec`'s
# "be counted short and still name what the fact used", and `DerivationSpec` green.
echo "################ 2-reach-stops-at-a-citation" >> "$LOG"
"$P" "$DERIVATION" \
  '    walk(theorem).foldLeft(Set.empty[Term]) { (found, node) =>
      if (node.hypotheses.isEmpty && wanted.contains(node.conclusion))' \
  '    own(theorem).foldLeft(Set.empty[Term]) { (found, node) =>
      if (node.hypotheses.isEmpty && wanted.contains(node.conclusion))' \
  -- ./tools/sbt -batch "$KERNEL" "$REACH" >> "$LOG" 2>&1
echo "### exit $? for 2-reach-stops-at-a-citation" >> "$LOG"

# 3. Card 2a48d6d0's assertion in `ReachSpec`, that a report on the corpus reads fewer nodes than
# a checker replays. The accounting walks follow a citation's premise, which is the state before
# `docs/adr/0047`; the size then counts every replayed step. Expect red on "read less than it
# replays", at `read should be < whole`.
echo "################ 3-accounting-walks-through" >> "$LOG"
"$P" "$DERIVATION" \
  'case Citation(_, _) => Nil' \
  'case Citation(_, fact) => List(fact)' \
  -- ./tools/sbt -batch 'tactics/testOnly garden.xeno.symbolum.tactics.ReachSpec -- -z "read less than it replays"' >> "$LOG" 2>&1
echo "### exit $? for 3-accounting-walks-through" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
