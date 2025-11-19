# Code Improvement Action Plan

**Status:** Ready for implementation
**Estimated Total Effort:** 44-72 hours
**Priority Order:** Critical → High → Medium

---

## Phase 1: Critical Fixes (Must Do)

### Issue #1: Replace Array with Vector in Case Classes
**Priority:** 🔴 CRITICAL
**Effort:** 4-6 hours
**Files:** Add.scala, Mul.scala, Div.scala, Sub.scala

**Current:**
```scala
final case class Add(exprs: Array[Expr]) extends Expr
```

**Fixed:**
```scala
final case class Add(exprs: Vector[Expr]) extends Expr {
  // Remove toString workarounds - structural equality now works!
}
```

**Changes Required:**
1. Replace `Array` with `Vector` in all case classes
2. Update all Array construction to Vector:
   - `Array(...)` → `Vector(...)`
   - `exprs.toArray` → `exprs.toVector`
3. Remove toString-based grouping workarounds
4. Update tests for new equality semantics

**Migration Path:**
```scala
// Option A: Direct replacement (breaking change)
final case class Add(exprs: Vector[Expr]) extends Expr

// Option B: Gradual migration (add companion apply)
final case class Add private (exprs: Vector[Expr]) extends Expr
object Add {
  def apply(exprs: Array[Expr]): Add = new Add(exprs.toVector)
  def apply(exprs: Vector[Expr]): Add = new Add(exprs)
}
```

**Benefits:**
- Structural equality works correctly
- Remove O(n²) toString comparisons
- 10-100x performance improvement in grouping operations

---

### Issue #2: Implement Structural Equality
**Priority:** 🔴 CRITICAL
**Effort:** 3-4 hours
**Files:** Add.scala, Mul.scala

**Current:**
```scala
// Add.scala:91
val grouped = terms.groupBy { term =>
  val (_, base) = extractCoeffAndBase(term)
  base.toString  // ❌ O(n) per comparison
}
```

**Fixed:**
```scala
// Create proper structural key
case class StructuralKey(expr: Expr) {
  override def equals(obj: Any): Boolean = obj match {
    case StructuralKey(other) => structurallyEqual(expr, other)
    case _ => false
  }

  override def hashCode(): Int = structuralHash(expr)

  private def structurallyEqual(a: Expr, b: Expr): Boolean = (a, b) match {
    case (Add(as), Add(bs)) => as.length == bs.length && as.zip(bs).forall { case (x, y) => structurallyEqual(x, y) }
    case (Mul(as), Mul(bs)) => as.length == bs.length && as.zip(bs).forall { case (x, y) => structurallyEqual(x, y) }
    case (Num(an, ad), Num(bn, bd)) => an == bn && ad == bd
    case (Var(a), Var(b)) => a == b
    case _ => a == b
  }

  private def structuralHash(e: Expr): Int = e match {
    case Add(exprs) => exprs.map(structuralHash).foldLeft(1)(_ * 31 + _)
    case Mul(exprs) => exprs.map(structuralHash).foldLeft(2)(_ * 31 + _)
    case Num(n, d) => (n, d).hashCode()
    case Var(name) => name.hashCode()
    case _ => e.hashCode()
  }
}

// Usage:
val grouped = terms.groupBy(term => StructuralKey(extractCoeffAndBase(term)._2))
```

**Note:** This becomes unnecessary if Issue #1 is fixed first (Vector gives structural equality).

---

### Issue #3: Add Expansion Limits
**Priority:** 🔴 CRITICAL
**Effort:** 2-3 hours
**File:** Mul.scala, SimplificationConfig.scala

**Current:**
```scala
def cartesian[T](xss: List[List[T]]): List[List[T]] = xss match {
  case Nil => List(Nil)
  case h :: t =>
    for {
      x <- h
      xs <- cartesian(t)
    } yield x :: xs
}
```

**Fixed:**
```scala
// Add to SimplificationConfig.scala
case class SimplificationConfig(
  enabledRules: List[SimplificationRule] = SimplificationConfig.DefaultRules,
  maxExpansionTerms: Int = 1000  // NEW
)

// Update Mul.scala
private def expandDistribute(children: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
  val termSets: Vector[Vector[Expr]] = children.map {
    case Add(ts) => ts
    case other => Vector(other)
  }

  // Calculate total terms before expanding
  val totalTerms = termSets.map(_.length).product

  if (totalTerms > config.maxExpansionTerms) {
    // Don't expand - return as-is
    return Mul(children).simplify(config)
  }

  val hasAddition = termSets.exists(_.length > 1)
  if (!hasAddition || !config.isEnabled(DistributeProduct))
    return Mul(children).simplify(config)

  // Safe to expand
  val combos = cartesian(termSets.toList)
  val distributedTerms = combos.map(factors => Mul(factors.toVector).simplify(config)).toVector
  Add(distributedTerms).simplify(config)
}
```

**Benefits:**
- Prevents OOM on large expressions
- Configurable limits per use case
- Graceful degradation

---

### Issue #4: Seal Expr Trait
**Priority:** 🔴 CRITICAL
**Effort:** 30 minutes
**File:** Expr.scala

**Current:**
```scala
trait Expr {
  def precedence: Int = 10
  // ...
}
```

**Fixed:**
```scala
sealed trait Expr {
  def precedence: Int = 10
  // ...
}
```

**Benefits:**
- Compiler enforces exhaustive pattern matching
- Catch missing cases at compile time
- Better IDE support (autocomplete)

**Test:**
```scala
def analyze(e: Expr): String = e match {
  case Add(_) => "addition"
  case Mul(_) => "multiplication"
  // Compiler warns if cases are missing!
}
```

---

## Phase 2: High Priority Fixes

### Issue #5: Refactor Add.simplify
**Priority:** 🟡 HIGH
**Effort:** 6-8 hours
**File:** Add.scala

**Current:** 217-line god method

**Fixed:**
```scala
def simplify(implicit config: SimplificationConfig): Expr = {
  simplifyPipeline(
    flattenAndRemoveIdentity,
    mergeFractions,
    collectTerms,
    factorTerms,
    combineNumerics
  )
}

private def flattenAndRemoveIdentity(exprs: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
  val flattened = if (config.isEnabled(FlattenOperations)) {
    exprs.flatMap {
      case Add(inner) => inner
      case other => Vector(other)
    }
  } else exprs

  if (config.isEnabled(RemoveIdentity))
    flattened.filterNot(_ == Num(0))
  else
    flattened
}

private def mergeFractions(exprs: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
  if (!config.isEnabled(MergeFractionsLCD)) return exprs

  mergeFractionsLCD(exprs) match {
    case Some(merged) => Vector(merged)
    case None => exprs
  }
}

// ... similar for other steps

private def simplifyPipeline(steps: (Vector[Expr] => Vector[Expr])*)(implicit config: SimplificationConfig): Expr = {
  val simplified = exprs.map(_.simplify)
  val result = steps.foldLeft(simplified) { (acc, step) => step(acc) }

  result.length match {
    case 0 => Num(0)
    case 1 => result(0)
    case _ => Add(result)
  }
}
```

**Benefits:**
- Each method < 30 lines
- Single Responsibility Principle
- Easier to test each step
- Easier to debug
- Better composition

---

### Issue #6: Consolidate Fraction Utilities
**Priority:** 🟡 HIGH
**Effort:** 2-3 hours
**Files:** Num.scala, Add.scala

**Current:** Duplicated in multiple places

**Fixed:**
```scala
// Num.scala companion object
object Num {
  /** Greatest common divisor using Euclidean algorithm */
  def gcd(a: Double, b: Double): Double = {
    @tailrec
    def loop(x: Double, y: Double): Double =
      if (math.abs(y) < NumericConstants.TOLERANCE) x
      else loop(y, x % y)
    loop(math.abs(a), math.abs(b))
  }

  /** Least common multiple */
  def lcm(a: Double, b: Double): Double = {
    if (a == 0.0 || b == 0.0) 0.0
    else math.abs(a * b) / gcd(a, b)
  }

  /** Add two fractions */
  def addFractions(a: Num, b: Num): Num = {
    val newNum = a.numerator * b.denominator + b.numerator * a.denominator
    val newDen = a.denominator * b.denominator
    Num(newNum, newDen)
  }

  /** Check if a double is a whole number */
  def isWhole(d: Double): Boolean =
    math.abs(d % 1.0) < NumericConstants.TOLERANCE
}

// NumericConstants.scala (new file)
object NumericConstants {
  val TOLERANCE: Double = 1e-10
  val MAX_ITERATIONS: Int = 100
  val DEFAULT_MAX_EXPANSION_TERMS: Int = 1000
}
```

**Update usage:**
```scala
// Add.scala - replace all instances
import Num.{gcd, lcm, addFractions, isWhole}

private def collectLikeTerms(...): Vector[Expr] = {
  // ...
  val totalCoeff = coeffsAndBases.map(_._1).reduce(addFractions).simplify
  // ...
}
```

---

### Issue #7: Add Input Validation
**Priority:** 🟡 HIGH
**Effort:** 2-3 hours
**Files:** All expression classes

**Current:** No validation

**Fixed:**
```scala
final case class Div(exprs: Vector[Expr]) extends Expr {
  require(exprs.length >= 2, s"Division requires at least 2 operands, got ${exprs.length}")
  require(exprs.nonEmpty, "Division operands cannot be empty")

  // ...
}

final case class Num(numerator: Double, denominator: Double = 1.0) extends Expr {
  require(!numerator.isNaN, "Numerator cannot be NaN")
  require(!numerator.isInfinity, "Numerator cannot be infinite")
  require(!denominator.isNaN, "Denominator cannot be NaN")
  require(!denominator.isInfinity, "Denominator cannot be infinite")
  require(denominator != 0.0, "Denominator cannot be zero")

  // ...
}

// CollatzSeries.scala
def binomial(n: Int, k: Int): Long = {
  require(n >= 0, s"n must be non-negative, got $n")
  require(k >= 0, s"k must be non-negative, got $k")

  if (k > n || k < 0) 0L
  else if (k == 0 || k == n) 1L
  else {
    // Add overflow detection
    var result = 1L
    for (i <- 1 to math.min(k, n - k)) {
      val nextResult = result * (n - i + 1) / i
      require(nextResult >= result || i == 1, s"Binomial coefficient overflow at C($n,$k)")
      result = nextResult
    }
    result
  }
}
```

---

### Issue #8: Extract Magic Numbers
**Priority:** 🟡 HIGH
**Effort:** 1 hour
**Files:** All

**See Issue #6 for NumericConstants object**

**Update all usage:**
```scala
// Before:
if (math.abs(d - firstDen) < 1e-10)

// After:
import NumericConstants._
if (math.abs(d - firstDen) < TOLERANCE)

// Before:
def fullSimplify(..., maxIter: Int = 100): Expr

// After:
def fullSimplify(..., maxIter: Int = MAX_ITERATIONS): Expr
```

---

### Issue #9: Standardize Error Handling
**Priority:** 🟡 HIGH
**Effort:** 3-4 hours
**Files:** All

**Decision:** Use exceptions for programming errors, Either for expected failures

**Fixed:**
```scala
// Programming errors: require/IllegalArgumentException
final case class Div(exprs: Vector[Expr]) extends Expr {
  require(exprs.length >= 2)  // Programming error
  // ...
}

// Runtime errors: custom exception hierarchy
sealed abstract class ExpressionError(message: String) extends Exception(message)
case class DivisionByZero(expr: String) extends ExpressionError(s"Division by zero in: $expr")
case class UndefinedVariable(name: String) extends ExpressionError(s"Variable not defined: $name")
case class NumericOverflow(operation: String) extends ExpressionError(s"Numeric overflow in: $operation")

// Expected failures: Either
def mergeFractionsLCD(terms: Vector[Expr])(implicit config: SimplificationConfig): Option[Expr] = {
  // Keep as Option - this is an expected "can't merge" case
}

// Update eval to use Either
def eval(variables: Map[String, Double]): Either[ExpressionError, Double]
```

---

### Issue #10: Fuse Array Traversals
**Priority:** 🟡 HIGH
**Effort:** 2-3 hours
**File:** Add.scala

**Current:** Multiple separate traversals

**Fixed:**
```scala
// Use single traversal with accumulator
case class SimplifyAccumulator(
  nums: Vector[Num] = Vector.empty,
  divs: Vector[Div] = Vector.empty,
  others: Vector[Expr] = Vector.empty
) {
  def add(e: Expr): SimplifyAccumulator = e match {
    case n: Num => copy(nums = nums :+ n)
    case d: Div => copy(divs = divs :+ d)
    case other => copy(others = others :+ other)
  }
}

def simplify(implicit config: SimplificationConfig): Expr = {
  val simplified = exprs.map(_.simplify)

  // Single pass!
  val acc = simplified.foldLeft(SimplifyAccumulator()) { (acc, expr) =>
    expr match {
      case Add(inner) if config.isEnabled(FlattenOperations) =>
        inner.foldLeft(acc)((a, e) => if (e != Num(0)) a.add(e) else a)
      case Num(0) if config.isEnabled(RemoveIdentity) =>
        acc
      case other =>
        acc.add(other)
    }
  }

  // Process accumulated results
  processAccumulator(acc)
}
```

---

## Phase 3: Medium Priority

### Issue #11: Improve Variable Names
**Priority:** 🟢 MEDIUM
**Effort:** 1-2 hours

**Changes:**
```scala
// Before:
val (an, ad) = ...
val (bn, bd) = ...

// After:
val (aNumerator, aDenominator) = ...
val (bNumerator, bDenominator) = ...

// Before:
def prod(xs: Seq[Expr]): Expr

// After:
def buildProduct(expressions: Seq[Expr]): Expr

// Before:
val s = expr.simplify

// After:
val simplified = expr.simplify
```

---

### Issue #12: Migrate to ScalaTest
**Priority:** 🟢 MEDIUM
**Effort:** 6-8 hours

**Add to build.sbt:**
```scala
libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.2.17" % Test,
  "org.scalacheck" %% "scalacheck" % "1.17.0" % Test,
  "org.scalatestplus" %% "scalacheck-1-17" % "3.2.17.0" % Test
)
```

**Create test structure:**
```scala
// src/test/scala/symbolicas/ExprSpec.scala
class ExprSpec extends AnyFlatSpec with Matchers with ScalaCheckPropertyChecks {

  "Add.simplify" should "combine like terms" in {
    val x = Var("x")
    val expr = Add(Vector(x, Mul(Vector(Num(2), x))))
    expr.simplify.toString shouldBe "3 * x"
  }

  it should "preserve fractions when configured" in {
    val expr = Add(Vector(Num(1, 2), Num(1, 3)))
    val result = expr.simplify(SimplificationConfig.Minimal)
    // Assert fraction preservation
  }

  it should "satisfy associativity property" in {
    forAll { (a: Int, b: Int, c: Int) =>
      whenever(a != 0 && b != 0 && c != 0) {
        val e1 = Add(Vector(Num(a), Add(Vector(Num(b), Num(c)))))
        val e2 = Add(Vector(Add(Vector(Num(a), Num(b))), Num(c)))
        e1.fullSimplify shouldBe e2.fullSimplify
      }
    }
  }
}
```

---

### Issue #13: Enhance Documentation
**Priority:** 🟢 MEDIUM
**Effort:** 3-4 hours

**Add complexity analysis:**
```scala
/**
 * Simplifies an addition expression.
 *
 * @param config Simplification configuration
 * @return Simplified expression
 *
 * @note Time Complexity:
 *   - Best case: O(n) for flat additions
 *   - Average case: O(n log n) with proper structural equality
 *   - Worst case: O(n²) for deeply nested expressions
 *   where n is the total number of nodes in the expression tree
 *
 * @note Space Complexity: O(n) for intermediate results
 *
 * @note Thread Safety: This method is thread-safe as all operations
 *   are performed on immutable data structures.
 *
 * @example {{{
 *   val expr = Add(Vector(Var("x"), Num(2), Var("x")))
 *   expr.simplify // Returns: Add(Vector(Mul(Vector(Num(2), Var("x"))), Num(2)))
 * }}}
 */
def simplify(implicit config: SimplificationConfig): Expr = {
  // ...
}
```

---

## Implementation Order

### Sprint 1 (Week 1): Critical Foundations
- [ ] Day 1-2: Issue #1 (Array → Vector)
- [ ] Day 2-3: Issue #4 (Seal Expr)
- [ ] Day 3-4: Issue #7 (Input validation)
- [ ] Day 4-5: Issue #3 (Expansion limits)

### Sprint 2 (Week 2): Performance & Quality
- [ ] Day 1-3: Issue #5 (Refactor Add.simplify)
- [ ] Day 3-4: Issue #6 (Consolidate utilities)
- [ ] Day 4-5: Issue #8 (Extract constants)

### Sprint 3 (Week 3): Testing & Polish
- [ ] Day 1-2: Issue #10 (Fuse traversals)
- [ ] Day 2-4: Issue #12 (ScalaTest migration)
- [ ] Day 4-5: Issue #9 (Error handling)

### Sprint 4 (Week 4): Documentation & Cleanup
- [ ] Day 1-2: Issue #13 (Documentation)
- [ ] Day 2-3: Issue #11 (Variable names)
- [ ] Day 3-5: Code review, cleanup, final testing

---

## Success Metrics

### Code Quality
- [ ] Cyclomatic complexity < 10 for all methods
- [ ] No method > 50 lines
- [ ] All magic numbers extracted
- [ ] Consistent error handling

### Performance
- [ ] collectLikeTerms: O(n log n) or better
- [ ] No toString for equality
- [ ] Expansion limits enforced
- [ ] Single-pass simplification

### Testing
- [ ] Test coverage ≥ 80%
- [ ] Property-based tests for laws
- [ ] All edge cases covered
- [ ] Automated CI/CD

### Documentation
- [ ] All public APIs have Scaladoc
- [ ] Complexity analysis documented
- [ ] Examples in all docs
- [ ] Architecture guide

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Breaking changes in Phase 1 | High | High | Version bump to 3.0, migration guide |
| Performance regression | Medium | Medium | Benchmark before/after |
| Test migration issues | Medium | Low | Run both old and new tests in parallel |
| Time overruns | Medium | Low | Prioritize critical fixes first |

---

## Next Steps

1. **Create branch:** `git checkout -b feature/code-quality-improvements`
2. **Start with Issue #4** (quickest win - seal trait)
3. **Then Issue #7** (validation - catches bugs early)
4. **Then Issue #1** (biggest impact - Array to Vector)
5. **Iterate** through remaining issues in priority order

## Questions to Resolve

1. **Breaking Changes:** Is v3.0 acceptable for Array → Vector migration?
2. **Testing:** Should we keep .sc scripts in addition to ScalaTest?
3. **Error Handling:** Exceptions vs Either - which for eval()?
4. **Expansion Limits:** Default to 1000, 10000, or configurable only?
5. **Performance:** Is memoization needed, or are structural fixes enough?

---

**Last Updated:** 2025-11-19
**Status:** Ready for implementation
**Approver:** [Pending]
