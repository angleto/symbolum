#!/bin/sh
# Fire the guards of card e49e4d76, a certificate found and not rebuilt, at the defects they are for.
#
# `Linarith` finds a certificate with an untrusted search and rebuilds it in the kernel. Until
# 2026-09-25 a rebuilding that the kernel refused came out as whatever the refusing step said, a
# RING `NotEqualTo` at the first level, and inside an escalation as the refusal from before it,
# `DoesNotFollow`: both standing `Decided`, so a goal whose proof had just been found was reported
# as decided not to follow. `NotRebuilt` is what comes out now, at both levels, and it is never
# decided.
#
# 1 takes the repair away at the place the goal of the new `LinarithSpec` test meets it, which is
# the rebuilding of a contradiction and not of a certificate for the goal: the refusal measured on
# that goal is RING's `... is not equal to real_zero`, the vanishing check in `absurdity`. The first
# version of this file took it away at the other site, and 1 came back green with the tree as it
# was, which is how the site was found. On a tree without card ba9a1e99's repair 1 is the
# observation the new test owes: red, with `DoesNotFollow`.
# 2 breaks every rebuilding of a certificate for a goal, which no test can do from inside the run
# it is part of. Measured on its first run: the 29 tests that prove something fail naming
# `NotRebuilt`, and so do two that expect `DoesNotFollow`, because those goals are refused through
# the three-way split, one of whose cases finds a certificate the broken rebuilding refuses. That
# is the design and not a slip: a split that could not settle one case has not searched its own
# fragment to the end, so it cannot say the goal is outside it.
# 1-over-2 is 2 with the repair also taken away at the certificate site: the proving tests then
# fail with RING's `NotEqualTo`, standing decided and naming neither goal nor certificate, which is
# the first-level symptom the card names; and an assertion that was already there catches it by
# name, "a proof is not a decision", since `x < y ==> x < y` comes back decided. The two refusals
# through the split go green again, and that is the defect too: their case's refusal is swallowed
# into the `DoesNotFollow` they expect.
# 3 and 1-over-3 are what keeps the new test observable once ba9a1e99's repair has landed, when its
# goal is proved and 1 has nothing to take away: 3 makes RING refuse every contradiction's
# vanishing check, as it refused at `57a2276d`, and 1-over-3 also takes the repair away there.
#
# The strings are literal and were unique when this was written. perturb.sh REFUSES a perturbation
# that did not apply rather than running against unperturbed code.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

LOG="$OUT/certificate-not-rebuilt.log"
SOURCE=modules/theories/src/main/scala/garden/xeno/symbolum/theories/Linarith.scala
SPECS='theories/testOnly garden.xeno.symbolum.theories.LinarithSpec'

WRAPPED='case Some(certificate) => rebuilt(conclusion, fromCertificate(certificate, facts, assumed, conclusion))'
BARE='case Some(certificate) => fromCertificate(certificate, facts, assumed, conclusion)'
ABSURD='case Some(certificate) => rebuilt(conclusion, absurdity(certificate, facts, assumed, conclusion))'
ABSURD_BARE='case Some(certificate) => absurdity(certificate, facts, assumed, conclusion)'
VANISH='vanishes <- ring.prove(equation)'
REFUSED='vanishes <- ring.prove(equation).flatMap(_ => Left(NotEqualTo(sum, zero)))'
SCALE='shifted <- shiftToGoal(combined, certificate.scale, conclusion)'
WRONG='shifted <- shiftToGoal(combined, certificate.scale + 1, conclusion)'

run() { n="$1"; shift
  echo "################ $n" >> "$LOG"
  "$@" >> "$LOG" 2>&1
  echo "### exit $? for $n" >> "$LOG"
}

# 0. THE CONTROL.
run "0-control" ./tools/sbt -batch "$SPECS"

# 1. The repair taken away where the goal of the new test meets it.
# Expect red on: "report a certificate it found and could not rebuild", naming DoesNotFollow, on a
# tree where ba9a1e99 has not landed. On a tree where it has, the goal is proved and 1 is green.
run "1-not-wrapped" "$P" "$SOURCE" "$ABSURD" "$ABSURD_BARE" -- ./tools/sbt -batch "$SPECS"

# 2. Every rebuilding of a certificate for a goal refused, by a scale it was not taken at.
# Expect red on: 29 tests that prove a goal and the two refusals that go through the split, each
# failing with `NotRebuilt`; green on the new test and on every refusal not reached through a split.
# Measured twice, 31 of 48 before card ba9a1e99 landed and 31 of 50 after it.
run "2-rebuilding-refused" "$P" "$SOURCE" "$SCALE" "$WRONG" -- ./tools/sbt -batch "$SPECS"

# 1 over 2. The repair taken away at the certificate site while every rebuilding there is refused.
# Expect red on: the 29 proving tests, now with RING's `NotEqualTo`, decided and naming no goal,
# and "say in the type which standing it ended in" at "a proof is not a decision"; green on the two
# refusals through the split. 30 of 50, measured.
run "1-over-2" "$P" "$SOURCE" "$SCALE" "$WRONG" -- "$P" "$SOURCE" "$WRAPPED" "$BARE" -- ./tools/sbt -batch "$SPECS"

# 3. Every rebuilding of a contradiction refused by RING, the way the one that started this was.
# Expect red on: the tests whose goals rest on a contradiction, naming `NotRebuilt`; green on the
# new test, whose goal now comes back as the certificate's refusal rather than as a theorem. 3 of
# 50, measured: "prove whatever they are asked" and card ba9a1e99's two.
run "3-contradiction-refused" "$P" "$SOURCE" "$VANISH" "$REFUSED" -- ./tools/sbt -batch "$SPECS"

# 1 over 3. The repair taken away at the contradiction site while every contradiction is refused.
# Expect red on: the new test, with `DoesNotFollow` on its true goal, on any tree, and the three of 3.
# 4 of 50, measured.
run "1-over-3" "$P" "$SOURCE" "$VANISH" "$REFUSED" -- "$P" "$SOURCE" "$ABSURD" "$ABSURD_BARE" -- ./tools/sbt -batch "$SPECS"

echo "### all fired" >> "$LOG"
git status --porcelain >> "$LOG"
