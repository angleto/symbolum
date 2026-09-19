#!/bin/sh
# Fire the guards of card 79ff6dbe (the two censuses of `RewriteSpec` and the tables that absorb a
# repeated key) at the two defects they are written for.
#
# The defects, both latent when the guards landed on 2026-09-19, which is why a harness is the only
# way to see either guard work:
#
#   1. Both censuses in `RewriteSpec` walked `Vector("kernel", "logic", "theories", "tactics",
#      "core", "checker")`. Measured against `build.sbt`: three of those six declare no path to
#      `logic` and cannot name `Rewrite` at all, and `examples` and `dist`, which can, were in
#      neither list. Both censuses were green throughout, because a scan that does not look
#      somewhere reports nothing from there.
#   2. `ReviewedCallSites`, `Classified`, `Unrendered`, `ProseField` and `Accounted` were `Map(...)`
#      literals. A repeated key is absorbed, keeping the last, and **every assertion those five
#      tables carry goes on passing**: the row is still found and still reached. In
#      `ChainCoverageSpec` the absorbed row can carry a different `Standing`, so the contradiction
#      between two readings of one file is what disappears.
#
# Each perturbation below restores one of those defects. Reproduced 2026-09-19 in
# /Users/angelo/data/WORK/symbolum-wt/rewrite-census, control green at 28 + 4 + 11 tests:
#
#   1  `reached` came back as the six-name list and the agreement failed, naming the five modules
#      it no longer reached: dist, examples, mark, sat, scan.
#   2a two tests red -- the new guard AND the agreement with `Chain`, which is what corrected the
#      claim this harness was first written with.
#   2b exactly one test red, the new guard, the other three green.
#   3  one test red, naming `(Bounded.scala,position)`; 121 against 122.
#
# Reproduced again 2026-09-19 in /Users/angelo/data/WORK/symbolum-wt/verify-79ff6dbe at `5035782`,
# verifying the card rather than delivering it, same four outcomes and the same control. Four more
# were added there and are 4 to 7 below: three because the card landed SIX guards of the repeated
# key and this harness fired three of them, and one because a guard seen only passing is a guard
# nobody has watched work.
#
#   4  one test red, naming `(Prove.scala,why)`; 6 against 7.
#   5  one test red, naming `DoesNotFollow`; 9 against 10.
#   6  one test red, naming `Induct.scala`.
#   7  **exit 0, 28 green, and that is the finding rather than the control.** Perturbation 1 puts
#      the list back where the walk is DEFINED, and the agreement sees it. Number 7 leaves
#      `moduleRoots` alone and gives the first census a six-name walk of its OWN, three lines below
#      the agreement that is supposed to be watching, and nothing anywhere goes red: the four
#      positive controls of that census (`Induct`, `Family`, `Order`, `Magnitude`) all sit inside
#      the six names, so the census reports the same files it always did. What the new test asserts
#      is that `mainSources` reaches every module, and it cannot assert that a census uses it. That
#      is the door the defect of 2026-09-18 came through -- the second census copied the first's
#      list -- and it is open, one call site wide. It is recorded here rather than repaired,
#      because the repair is the author's and a measurement is what a verification leaves behind.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
WT=${WT:-$ROOT}
OUT=${OUT:-$WT/scratch/verify/out}; mkdir -p "$OUT"
P=${PERTURB:?set PERTURB to a perturbation tool that captures bytes, substitutes,
restores and verifies the restore; see tools/verify/README.md}
cd "$WT" || exit 2

REWRITE=modules/logic/src/test/scala/garden/xeno/symbolum/logic/RewriteSpec.scala
CHAIN=modules/theories/src/test/scala/garden/xeno/symbolum/theories/ChainCoverageSpec.scala
NOTATION=modules/tactics/src/test/scala/garden/xeno/symbolum/tactics/NotationBoundarySpec.scala

# The control, which is not a formality: a red under a perturbation says nothing unless the same
# three commands are green without one.
./tools/sbt -batch \
  'logic/testOnly garden.xeno.symbolum.logic.RewriteSpec' \
  'theories/testOnly garden.xeno.symbolum.theories.ChainCoverageSpec' \
  'tactics/testOnly garden.xeno.symbolum.tactics.NotationBoundarySpec' \
  > "$OUT/0-control.log" 2>&1
echo "control exit $? (0 is the expected outcome)"
grep -E "Tests: " "$OUT/0-control.log"

# 1. The root list put back, exactly as it stood until 2026-09-19. `moduleRoots` is where the two
#    censuses now get their sources, so restoring the list restores the defect in both at once.
"$P" "$REWRITE" \
  '    val stream = java.nio.file.Files.list(java.nio.file.Paths.get("modules"))
    try
      stream
        .toArray
        .toVector
        .map(_.asInstanceOf[java.nio.file.Path].resolve("src/main"))
        .filter(java.nio.file.Files.isDirectory(_))
        .sortBy(_.toString)
    finally stream.close()' \
  '    Vector("kernel", "logic", "theories", "tactics", "core", "checker")
      .map(name => java.nio.file.Paths.get(s"modules/$name/src/main"))
      .filter(java.nio.file.Files.isDirectory(_))
      .sortBy(_.toString)' \
  -- ./tools/sbt -batch \
     'logic/testOnly garden.xeno.symbolum.logic.RewriteSpec' \
  > "$OUT/1-root-list.log" 2>&1
echo "1 root list: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|did not contain|was not equal|perturb:" "$OUT/1-root-list.log"

# 2. One file accounted for twice, with two different standings. TWO runs, and the pair is the
#    point rather than either of them: the first draft of this harness claimed the three older
#    assertions were blind to a duplicate, ran, and was contradicted by one of them.
#
#    2a. A file that IS in the chain, duplicated out of it. Expect TWO tests red: the new guard,
#        and "agree with `Chain` about which developments it builds", which reads the standings
#        and not only the names. This is the measurement that corrected the claim.
"$P" "$CHAIN" \
  '    "Bounded" -> InTheChain,' \
  '    "Bounded" -> InTheChain,
    "Bounded" -> NotADevelopment,' \
  -- ./tools/sbt -batch \
     'theories/testOnly garden.xeno.symbolum.theories.ChainCoverageSpec' \
  > "$OUT/2a-accounted-twice-in-chain.log" 2>&1
echo "2a accounted twice, in the chain: exit $? (1 expected; TWO tests red)"
grep -E "Tests: |\*\*\* FAILED|was not equal|named twice|perturb:" "$OUT/2a-accounted-twice-in-chain.log"

#    2b. A file that is NOT in the chain, duplicated between two standings that are both outside
#        it. Expect exactly ONE test red, the new guard, with the other three green. This is the
#        case the older assertions cannot see, and it is sixty of the sixty-seven entries.
"$P" "$CHAIN" \
  '    "Embedding" -> NotADevelopment,' \
  '    "Embedding" -> NotADevelopment,
    "Embedding" -> DeclaresNothing,' \
  -- ./tools/sbt -batch \
     'theories/testOnly garden.xeno.symbolum.theories.ChainCoverageSpec' \
  > "$OUT/2b-accounted-twice-outside.log" 2>&1
echo "2b accounted twice, outside the chain: exit $? (1 expected; exactly ONE test red)"
grep -E "Tests: |\*\*\* FAILED|was not equal|named twice|perturb:" "$OUT/2b-accounted-twice-outside.log"

# 3. The same for a classification table, where the two existing assertions are again about the
#    key and not about what the key maps to.
"$P" "$NOTATION" \
  '    ("Bounded.scala", "position") -> (Verdict.Number, "which instance of the walk"),' \
  '    ("Bounded.scala", "position") -> (Verdict.Number, "which instance of the walk"),
    ("Bounded.scala", "position") -> (Verdict.Name, "a second reading of the same site"),' \
  -- ./tools/sbt -batch \
     'tactics/testOnly garden.xeno.symbolum.tactics.NotationBoundarySpec' \
  > "$OUT/3-classified-twice.log" 2>&1
echo "3 classified twice: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|was not equal|repeated in|perturb:" "$OUT/3-classified-twice.log"

# 4. The second of the three tables in `NotationBoundarySpec`. The guard asserts each of the three
#    separately, and the three assertions run in order, so a duplicate in the second or the third
#    is only visible while the first is green: both were unobserved until this ran.
"$P" "$NOTATION" \
  '    ("Prove.scala", "why") -> (Verdict.Text, "Address.Nobody'"'"'s own sentence, passed through"),' \
  '    ("Prove.scala", "why") -> (Verdict.Text, "Address.Nobody'"'"'s own sentence, passed through"),
    ("Prove.scala", "why") -> (Verdict.Name, "a second reading of the same site"),' \
  -- ./tools/sbt -batch \
     'tactics/testOnly garden.xeno.symbolum.tactics.NotationBoundarySpec' \
  > "$OUT/4-unrendered-twice.log" 2>&1
echo "4 unrendered twice: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|was not equal|repeated in|perturb:" "$OUT/4-unrendered-twice.log"

# 5. The third of the three, whose value is a position rather than a verdict. Duplicating a row
#    leaves `Describes.subsetOf(ProseField.keySet)` and the floor over `Describes` both true, so
#    the size equality is the only thing that can see it.
"$P" "$NOTATION" \
  '    "DoesNotFollow" -> 1,' \
  '    "DoesNotFollow" -> 1,
    "DoesNotFollow" -> 0,' \
  -- ./tools/sbt -batch \
     'tactics/testOnly garden.xeno.symbolum.tactics.NotationBoundarySpec' \
  > "$OUT/5-prose-field-twice.log" 2>&1
echo "5 prose field twice: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|was not equal|repeated in|perturb:" "$OUT/5-prose-field-twice.log"

# 6. `RewriteSpec`'s own table, which is the one the census reads. A duplicated file name leaves
#    both of the census's assertions passing -- the file is still found and still reviewed -- so
#    the review a reader believes is written here is what goes.
"$P" "$REWRITE" \
  '    "Induct.scala" ->' \
  '    "Induct.scala" -> "a second reading of the same file",
    "Induct.scala" ->' \
  -- ./tools/sbt -batch \
     'logic/testOnly garden.xeno.symbolum.logic.RewriteSpec' \
  > "$OUT/6-reviewed-twice.log" 2>&1
echo "6 reviewed call site twice: exit $? (1 is the expected outcome: the guard fired)"
grep -E "Tests: |\*\*\* FAILED|was not empty|file named twice|perturb:" "$OUT/6-reviewed-twice.log"

# 7. The one that is expected to be GREEN, and it is here because a green run is the finding. The
#    first census is given a walk of six names of its own and `moduleRoots` is left alone, which is
#    how the defect of 2026-09-18 actually arrived: not by editing the walk, but by writing a list
#    at a call site. Read the exit code against 1's: same defect, same file, opposite answer.
"$P" "$REWRITE" \
  '    val callers = mainSources
      .filter { path =>
        val text = new String(java.nio.file.Files.readAllBytes(path), "UTF-8")
        text.contains("Rewrite.rewrite(") ||' \
  '    val callers = Vector("kernel", "logic", "theories", "tactics", "core", "checker")
      .map(name => java.nio.file.Paths.get(s"modules/$name/src/main"))
      .filter(java.nio.file.Files.isDirectory(_))
      .flatMap { root =>
        val walk = java.nio.file.Files.walk(root)
        try
          walk.toArray.toVector
            .map(_.asInstanceOf[java.nio.file.Path])
            .filter(_.toString.endsWith(".scala"))
        finally walk.close()
      }
      .filter { path =>
        val text = new String(java.nio.file.Files.readAllBytes(path), "UTF-8")
        text.contains("Rewrite.rewrite(") ||' \
  -- ./tools/sbt -batch \
     'logic/testOnly garden.xeno.symbolum.logic.RewriteSpec' \
  > "$OUT/7-census-walks-its-own-list.log" 2>&1
echo "7 census 1 walks a list of its own: exit $? (0 is what was measured: nothing sees it)"
grep -E "Tests: |\*\*\* FAILED|was not equal|perturb:" "$OUT/7-census-walks-its-own-list.log"
