#!/bin/bash

# Runs the TestSymbolum demonstration from the examples module.
#
# This is not the test suite: that is `sbt test`. This builds the Collatz expressions by hand and
# prints them simplified, which is the quickest way to see the simplifier work on something that
# is not a one-liner.

set -e

echo "==================================="
echo "Symbolum demonstration runner"
echo "==================================="
echo ""

if command -v sbt &> /dev/null; then
    echo "[Method 1] Using SBT..."
    sbt "examples/runMain garden.xeno.symbolum.examples.TestSymbolum"
    exit 0
fi

# Fallback for a machine with a Scala compiler but no build tool. It compiles the library and the
# demonstrations together, because the demonstrations import the library and no single file can be
# run on its own.
if command -v scalac &> /dev/null && command -v scala &> /dev/null; then
    echo "[Method 2] Using scalac..."
    mkdir -p target/classes
    find modules/core/src/main/scala modules/examples/src/main/scala -name "*.scala" \
        -exec scalac -d target/classes {} +
    scala -cp target/classes garden.xeno.symbolum.examples.TestSymbolum
    exit 0
fi

echo ""
echo "ERROR: No Scala build tool found!"
echo ""
echo "Please install one of:"
echo "  - SBT: https://www.scala-sbt.org/download.html"
echo "  - Scala: https://www.scala-lang.org/download/"
echo ""
exit 1
