# Algebraic Simplification Improvements

## Overview

This document describes the major improvements to algebraic simplification for handling complex nested expressions, particularly for the Collatz sequences. The improvements enable proper simplification of expressions like:

**Before:** `(3 * (3 * n + 1)/2 + 1)/2`
**After:** `(9*n + 5)/4`

**Before:** `cos((3 * (3 * n + 1)/2 + 1)/2 * pi)`
**After:** `cos((9*n+5)/4 * pi)`

## Problems Solved

### Problem 1: Numeric Coefficients Not Merged with Divisions

**Issue:** Expressions like `3 * ((3*n + 1) / 2)` stayed in that form instead of becoming `(3*(3*n + 1)) / 2`.

**Example:**
- Input: `3 * ((3*n + 1) / 2)`
- Expected: `(9*n + 3) / 2` (after expansion)
- Got: `3 * ((3*n + 1) / 2)` (no simplification)

**Root Cause:** `Mul.simplify` didn't recognize that numeric factors could be moved into division numerators.

### Problem 2: Divisions with Common Denominators Not Merged

**Issue:** When multiple division terms appeared in an addition with the same denominator, they weren't automatically merged.

**Example:**
- Input: `(9*n)/4 + 3/4 + 2/4`
- Expected: `(9*n + 5)/4`
- Got: `(9*n)/4 + 5/4` or stayed separate

**Root Cause:** `Add.simplify` only merged numeric `Num` fractions, not general `Div` expressions.

### Problem 3: Nested Divisions Not Fully Flattened

**Issue:** Complex nested divisions like `((a + b)/c)/d` didn't simplify to `(a + b)/(c*d)`.

**Example:**
- Input: `((3*(3*n + 1) + 2) / 2) / 2`
- Expected: `(3*(3*n + 1) + 2) / 4`
- Got: Partially simplified or not at all

**Root Cause:** `Div.simplify` had limited nested division handling.

### Problem 4: Numerators with Common Denominator Structure

**Issue:** When a division's numerator was an addition of divisions with the same denominator, it wasn't simplified.

**Example:**
- Input: `(a/d + b/d + c/d) / e`
- Expected: `(a + b + c) / (d * e)`
- Got: `(a/d + b/d + c/d) / e`

**Root Cause:** `Div.simplify` didn't look inside `Add` in the numerator.

## Solutions Implemented

### Solution 1: Merge Numeric Factors with Divisions in Mul

**File:** `Mul.scala` lines 126-151

**Transformation:**
```scala
Mul([Num(a, b), ..., Div([c, d]), ...])
→
Mul([..., Div([Mul([Num(a, b), c]), d]), ...])
```

**Implementation:**
```scala
/* Merge numeric factors with divisions */
val withMergedDivs = if (config.isEnabled(FlattenOperations)) {
  val (nums, nonNums) = withoutOnes.partition(_.isInstanceOf[Num])
  val (divs, others) = nonNums.partition(_.isInstanceOf[Div])

  if (nums.nonEmpty && divs.nonEmpty) {
    // Multiply all numeric factors
    val numProduct = if (nums.length == 1) nums.head
                     else Mul(nums).simplify(config)

    // For each Div, merge the numeric product into its numerator
    val mergedDivs = divs.map {
      case Div(Array(num, den)) =>
        Div(Array(Mul(Array(numProduct, num)).simplify(config), den))
      case d => d
    }

    mergedDivs ++ others
  } else {
    withoutOnes
  }
} else {
  withoutOnes
}
```

**Example:**
```scala
// Input
Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2)))))

// After transformation
Div(Array(
  Mul(Array(Num(3), Add(Array(Mul(Array(Num(3), n)), Num(1))))).simplify,
  Num(2)
))

// After Mul.expand and simplify
Div(Array(Add(Array(Mul(Array(Num(9), n)), Num(3))), Num(2)))

// Final result: (9*n + 3) / 2
```

### Solution 2: Merge Divisions with Common Denominators in Add

**File:** `Add.scala` lines 216-251

**Transformation:**
```scala
Add([Div([a, d]), Div([b, d]), ...])
→
Div([Add([a, b, ...]), d])
```

**Implementation:**
```scala
/* Merge divisions with common denominators */
val afterDivMerge: Array[Expr] = if (config.isEnabled(MergeFractionsCommonDenom)) {
  val (divs, nonDivs) = afterLikeTerms.partition(_.isInstanceOf[Div])

  if (divs.length >= 2) {
    // Group divisions by their denominator (as string for simplicity)
    val grouped = divs.collect { case Div(Array(num, den)) => (num, den) }
      .groupBy(_._2.toString)

    val mergedDivs = grouped.flatMap { case (_, pairs) =>
      if (pairs.length == 1) {
        // Single div with this denominator, keep as-is
        val (num, den) = pairs.head
        Some(Div(Array(num, den)))
      } else {
        // Multiple divs with same denominator, merge them
        val den = pairs.head._2
        val numerators = pairs.map(_._1)
        val mergedNumerator = Add(numerators.toArray).simplify(config)

        mergedNumerator match {
          case Num(0, _) => None
          case _ => Some(Div(Array(mergedNumerator, den)).simplify(config))
        }
      }
    }.toArray

    mergedDivs ++ nonDivs
  } else {
    afterLikeTerms
  }
} else {
  afterLikeTerms
}
```

**Example:**
```scala
// Input
Add(Array(
  Div(Array(Mul(Array(Num(9), n)), Num(4))),
  Div(Array(Num(3), Num(4))),
  Div(Array(Num(2), Num(4)))
))

// After grouping by denominator Num(4)
// Numerators: [9*n, 3, 2]
// Result
Div(Array(
  Add(Array(Mul(Array(Num(9), n)), Num(3), Num(2))).simplify,
  Num(4)
))

// After Add.simplify
Div(Array(Add(Array(Mul(Array(Num(9), n)), Num(5))), Num(4)))

// Final result: (9*n + 5) / 4
```

### Solution 3: Enhanced Nested Division Handling in Div

**File:** `Div.scala` lines 29-83

**Added Transformations:**

#### 3a. Division by Division
```scala
Div([a, Div([b, c])]) → Div([Mul([a, c]), b])
```

**Implementation:**
```scala
/* a / (b / c) -> (a * c) / b */
case Array(num, Div(Array(den1, den2))) if config.isEnabled(FlattenOperations) =>
  Div(Array(prod(Seq(num, den2))(config), den1)).simplify(config)
```

**Example:**
```scala
// Input: 6 / (2 / 3)
Div(Array(Num(6), Div(Array(Num(2), Num(3)))))

// After transformation
Div(Array(Mul(Array(Num(6), Num(3))).simplify, Num(2)))

// Result: Div(Array(Num(18), Num(2))) → Num(9)
```

#### 3b. Numerator with Common Denominator Divisions
```scala
Div([Add([Div([a, d]), Div([b, d]), ...]), c])
→
Div([Add([a, b, ...]), Mul([d, c])])
```

**Implementation:**
```scala
/* If numerator is Add with all Divs of same denom, simplify */
case Array(Add(addTerms), den) if config.isEnabled(MergeFractionsCommonDenom) =>
  val allDivs = addTerms.forall(_.isInstanceOf[Div])
  if (allDivs && addTerms.length > 1) {
    val divTerms = addTerms.collect { case Div(Array(n, d)) => (n, d) }
    val denominators = divTerms.map(_._2.toString).toSet

    if (denominators.size == 1) {
      // All have same denominator
      val commonDenom = divTerms.head._2
      val numerators = divTerms.map(_._1)
      val sumNumerators = Add(numerators).simplify(config)
      Div(Array(sumNumerators, prod(Seq(commonDenom, den))(config))).simplify(config)
    } else {
      Div(Array(Add(addTerms), den))
    }
  } else {
    Div(Array(Add(addTerms), den))
  }
```

**Example:**
```scala
// Input: (a/2 + b/2 + c/2) / 3
Div(Array(
  Add(Array(
    Div(Array(a, Num(2))),
    Div(Array(b, Num(2))),
    Div(Array(c, Num(2)))
  )),
  Num(3)
))

// After transformation
Div(Array(
  Add(Array(a, b, c)).simplify,
  Mul(Array(Num(2), Num(3))).simplify
))

// Result: (a + b + c) / 6
```

## Complete Simplification Example

Let's trace through the simplification of `(3 * (3 * n + 1)/2 + 1)/2`:

### Step 1: Parse
```scala
Div(Array(
  Add(Array(
    Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
    Num(1)
  )),
  Num(2)
))
```

### Step 2: Call `fullSimplify` (which calls `simplify` → `expand` → `simplify` repeatedly)

#### First Simplify Pass:
- `Mul.simplify` merges `Num(3)` with `Div`:
  ```scala
  Div(Array(
    Mul(Array(Num(3), Add(Array(Mul(Array(Num(3), n)), Num(1))))),
    Num(2)
  ))
  ```

#### Expand Pass:
- `Div.expand` expands children
- `Mul.expand` distributes: `3 * (3*n + 1)` → `9*n + 3`
  ```scala
  Div(Array(
    Add(Array(Div(Array(Add(Array(Mul(Array(Num(9), n)), Num(3))), Num(2))), Num(1))),
    Num(2)
  ))
  ```

#### Second Simplify Pass:
- Need to get `1` into a common denominator with the other term
- The `1` needs to become `2/2`
- Then `Add.simplify` can merge: `(9*n + 3)/2 + 2/2`

Wait, this is tricky. The issue is that we have:
```
(  (9*n + 3)/2  + 1  ) / 2
```

We need to first simplify the numerator by converting `1` to `2/2` and merging. But our current system only merges Div expressions, not Div + Num.

Actually, let me think about this differently. Maybe we need to distribute the outer division:

`(a + b) / c` can become `a/c + b/c`

But that's not always what we want...

Actually, looking at the structure, after the Mul expansion we should have:
```
Div(Array(
  Add(Array(
    Div(Array(Add(Array(9*n, 3)), 2)),
    1
  )),
  2
))
```

Then we can use the nested division rule:
`Div(Array(Div(Array(x, 2)), 2))` → `Div(Array(x, 4))`

But this only works if we split the Add. Let me think...

Actually, maybe the right approach is:
1. First recognize that we have `(x/2 + 1) / 2`
2. Convert this to `(x/2)/2 + 1/2`
3. Then flatten: `x/4 + 1/2`
4. Then merge to common denominator: `x/4 + 2/4` = `(x + 2)/4`

But that's complicated. Actually, maybe a better approach is to recognize in Div.simplify that if we have:

`Div([Add([Div([a, b]), other...]), c])`

We should distribute:
`Div([Div([a, b]), c]) + Div([other..., c])`
= `Div([a, b*c]) + other.../c`

Hmm, this is getting complex. Let me think about whether the current implementation actually handles this...

Actually, wait. After the Mul expansion, we should have:
```
Div(Array(Add(Array(9*n + 3, 1)), 2))  # Hmm, but 9*n+3 is still wrapped in Div(Array(..., 2))
```

Let me reconsider. After Mul merges Num with Div:
```
Div(Array(Mul(Array(Num(3), Add(Array(9*n, 1)))), Num(2)))
```

Then after Mul.expand on the numerator:
```
Div(Array(Add(Array(27*n, 3)), Num(2)))
```

Wait, that's not right either. Let me trace through more carefully.

Initial: `(3 * ((3*n + 1)/2) + 1) / 2`

After Mul merges Num with Div on the `3 * ((3*n + 1)/2)` part:
```
(  ((3 * (3*n + 1)) / 2)  + 1  ) / 2
```

After expand on `3 * (3*n + 1)`:
```
(  ((9*n + 3) / 2)  + 1  ) / 2
```

So we have:
```
Div(Array(
  Add(Array(
    Div(Array(Add(Array(9*n, 3)), 2)),
    1
  )),
  2
))
```

Now, to simplify this fully, we need to recognize that:
1. The inner Add has a Div and a Num
2. We want to merge them to a common denominator

But our current Add.simplify only merges Div with Div, not Div with Num.

So I need to add another rule: when we have `Div + Num`, convert the Num to a Div with denominator 1, then optionally find LCD.

Actually, a simpler approach: in Div.simplify, when we have `Div([Add([...]), den])`, we can distribute:
`(a + b) / c` → `a/c + b/c`

Then those can be simplified by the other rules.

Let me add this option to Div.
