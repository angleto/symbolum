#!/bin/sh
# Fire the per-fact equality of the axioms the lists spend, card 9084078b.
#
# The claim `ListingSpec` makes about that test is that a fact which starts or stops spending
# choice, infinity or eta goes red naming itself. The equality it replaced was over the union of
# the per-fact sets, and every list fact spends choice and infinity, so one fact dropping either
# left the union unchanged and the test green: that is what the verification of 2026-09-25 found.
#
# No derivation of this repository can be made to stop spending choice by a string substitution
# that still builds, since every list fact rests on the naturals and the naturals are carved with
# choice. So the perturbation is in the MEASUREMENT: the set read for `LIST_CONS_LENGTH` loses
# choice, which is exactly what the test would read if that derivation had stopped spending it.
# That fires the assertion at the input it exists for; what it cannot fire is a derivation, and
# nothing here pretends otherwise.
#
# The control is the run before it, in the same tree, and it must be green.
#
# WHAT WAS SEEN, 2026-09-25, on `570e1e40` plus this change. Control green at 10 tests.
# Perturbation 1 red at exactly one test, the per-fact equality, 9 green beside it, with the clue
# reading `LIST_CONS_LENGTH: INFINITY; LIST_HEAD_CONS: INFINITY, SELECT; ...`. The SAME
# substitution applied to `ListingSpec` as it stood at `570e1e40`, where the assertion was over
# the union, was green at 10 tests with the informer printing that same `LIST_CONS_LENGTH:
# INFINITY`: the defect the verification named, seen rather than argued. Restore verified by the
# perturbation tool and by `cmp` against a copy.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SPECFILE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/ListingSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.ListingSpec'
LOG="$OUT/lists-eta-per-fact.log"

echo "################ 0-control" >> "$LOG"
./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 0-control" >> "$LOG"

# 1. One fact reads as having stopped spending choice, and every other fact is unchanged, so the
# union of the sets is still the three axioms. Expected: red at the per-fact equality, with the
# clue naming `LIST_CONS_LENGTH: INFINITY` and nothing else in the file red.
echo "################ 1-one-fact-stops-spending-choice" >> "$LOG"
"$P" "$SPECFILE" \
  'name -> listing.facts.get(name).toVector.flatMap(t => Derivation.axiomsOf(t).toVector).toSet' \
  'name -> listing.facts.get(name).toVector.flatMap(t => Derivation.axiomsOf(t).toVector).toSet.filterNot(a => name == Listing.ConsLength && a == choice)' \
  -- ./tools/sbt -batch "$SPEC" >> "$LOG" 2>&1
echo "### exit $? for 1-one-fact-stops-spending-choice" >> "$LOG"

cd "$WT" && git status --porcelain >> "$LOG"
