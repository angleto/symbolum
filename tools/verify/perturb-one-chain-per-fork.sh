#!/bin/sh
# Fire OneChainPerForkSpec, card 4222de0a: a second chain built in the shared test fork of theories.
#
# The spec reads the test sources of `theories` with their comments removed and fails when one of
# them calls `Chain.construct(`. That is a claim about where something is written, so what can fail
# it is writing it: a call appended to `ChainSpec`'s code must turn it red, and the same call inside
# a comment must not, since a file that explains why it builds no chain has to name the call.
#
# WHAT WAS SEEN, 2026-09-27, through scala-cli over the classes of the tree that landed this and by
# appending rather than substituting: clean green at 2 tests; the call in code red, naming
# `ChainSpec.scala`; the call in a comment green. This harness is the same three through sbt.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}

cd "$WT" || exit 2

SOURCE=modules/theories/src/test/scala/garden/xeno/symbolum/theories/ChainSpec.scala
SPEC='theories/testOnly garden.xeno.symbolum.theories.OneChainPerForkSpec'
LINE='class ChainSpec extends AnyFlatSpec with Matchers {'

echo "################ 0-control" >> "$OUT/one-chain.log"
./tools/sbt -batch "$SPEC" >> "$OUT/one-chain.log" 2>&1
echo "### exit $? for 0-control" >> "$OUT/one-chain.log"

# 1. A second chain in code, never called: the spec reads text, so an unreachable call is as much a
# call as a reachable one, and it must be red.
echo "################ 1-a-call-in-code" >> "$OUT/one-chain.log"
"$P" "$SOURCE" "$LINE" "object PerturbedChain { def second = Chain.construct(null) }
$LINE" -- ./tools/sbt -batch "$SPEC" >> "$OUT/one-chain.log" 2>&1
echo "### exit $? for 1-a-call-in-code" >> "$OUT/one-chain.log"

# 2. The same call in a comment: green, or the spec is reading prose as code.
echo "################ 2-a-call-in-a-comment" >> "$OUT/one-chain.log"
"$P" "$SOURCE" "$LINE" "// Chain.construct(null) named in a comment
$LINE" -- ./tools/sbt -batch "$SPEC" >> "$OUT/one-chain.log" 2>&1
echo "### exit $? for 2-a-call-in-a-comment" >> "$OUT/one-chain.log"
