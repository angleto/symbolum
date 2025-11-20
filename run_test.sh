#!/bin/bash

# Script to compile and run the TestSymbolicas program

set -e

echo "==================================="
echo "Symbolicas Test Runner"
echo "==================================="
echo ""

# Try Method 1: SBT (preferred)
if command -v sbt &> /dev/null; then
    echo "[Method 1] Using SBT..."
    sbt "runMain TestSymbolicas"
    exit 0
fi

# Try Method 2: Scala-CLI
if command -v scala-cli &> /dev/null; then
    echo "[Method 2] Using scala-cli..."
    scala-cli run src/main/scala/TestSymbolicas.scala
    exit 0
fi

# Try Method 3: scalac + scala
if command -v scalac &> /dev/null && command -v scala &> /dev/null; then
    echo "[Method 3] Using scalac..."
    mkdir -p target/classes
    find src/main/scala -name "*.scala" -exec scalac -d target/classes {} +
    scala -cp target/classes TestSymbolicas
    exit 0
fi

echo ""
echo "ERROR: No Scala build tool found!"
echo ""
echo "Please install one of:"
echo "  - SBT: https://www.scala-sbt.org/download.html"
echo "  - Scala-CLI: https://scala-cli.virtuslab.org/install"
echo "  - Scala: https://www.scala-lang.org/download/"
echo ""
exit 1
