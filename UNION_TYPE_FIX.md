# Union Type Compilation Errors - Fixed

## Problem

After merging the v2.0 simplification system changes into the v2.0 branch, Scala 3 compilation failed with union type errors in `Add.scala` and `Mul.scala`.

### Error Messages

```
/Users/angelo/data/WORK/symbolicas/src/main/scala/symbolicas/Add.scala:199:63
value length is not a member of Seq[symbolicas.Expr] | Array[symbolicas.Expr]

/Users/angelo/data/WORK/symbolicas/src/main/scala/symbolicas/Add.scala:200:52
value partition is not a member of Seq[symbolicas.Expr] | Array[symbolicas.Expr]

/Users/angelo/data/WORK/symbolicas/src/main/scala/symbolicas/Mul.scala:169:62
value ++ is not a member of (nums : Array[symbolicas.Expr]) | Array[symbolicas.Num]
```

## Root Cause

**Scala 3 Union Type Inference**

When conditional expressions have different types in their branches, Scala 3 creates a union type. This happened in several places:

### Issue 1: Add.scala line 192-196

```scala
val afterLikeTerms = if (config.isEnabled(CollectLikeTerms)) {
  collectLikeTerms(noZeros)(config)  // Returns Seq[Expr]
} else {
  noZeros  // Is Array[Expr]
}
// Result: afterLikeTerms has type Seq[Expr] | Array[Expr]
```

Since union types don't have common methods like `.length` or `.partition`, subsequent code failed to compile.

### Issue 2: Mul.scala line 168-169

```scala
val combined: Array[Expr] =
  (if (numericPart == one) nums else Array(numericPart)) ++ others
```

The type inference created `Array[Num] | Array[Expr]` because `nums` was inferred as `Array[Num]` from the partition.

## Solution

Add **explicit type annotations** to force type unification instead of union type creation.

### Fix 1: Add.scala - Line 192

**Before:**
```scala
val afterLikeTerms = if (config.isEnabled(CollectLikeTerms)) {
  collectLikeTerms(noZeros)(config)
} else {
  noZeros
}
```

**After:**
```scala
val afterLikeTerms: Array[Expr] = if (config.isEnabled(CollectLikeTerms)) {
  collectLikeTerms(noZeros)(config).toArray  // Convert Seq to Array
} else {
  noZeros
}
```

**Changes:**
1. Added explicit type annotation: `Array[Expr]`
2. Converted `Seq[Expr]` to `Array[Expr]` with `.toArray`
3. Ensures both branches return `Array[Expr]`

### Fix 2: Add.scala - Line 233

**Before:**
```scala
val combined = (if (numSum != 0.0) Seq(Num(numSum)) else Seq()) ++ others
```

**After:**
```scala
val combined: Array[Expr] = (if (numSum != 0.0) Array[Expr](Num(numSum)) else Array.empty[Expr]) ++ others
```

**Changes:**
1. Added explicit type annotation: `Array[Expr]`
2. Changed `Seq` to `Array[Expr]` with explicit type parameter
3. Changed `Seq()` to `Array.empty[Expr]`

### Fix 3: Add.scala - Line 201, 245

**Before:**
```scala
if (factored != Add(afterLikeTerms.toArray)) {
```

**After:**
```scala
if (factored != Add(afterLikeTerms)) {
```

**Reason:** Since `afterLikeTerms` is now `Array[Expr]`, no need for `.toArray` conversion.

### Fix 4: Mul.scala - Line 169

**Before:**
```scala
val combined: Array[Expr] =
  (if (numericPart == one) nums else Array(numericPart)) ++ others
```

**After:**
```scala
val combined: Array[Expr] =
  (if (numericPart == one) nums else Array[Expr](numericPart)) ++ others
```

**Changes:**
1. Added explicit type parameter: `Array[Expr](numericPart)`
2. Forces both branches to return `Array[Expr]`

## Why This Works

### Scala 3 Type Inference

Scala 3's type inference is more precise than Scala 2, which can create union types in ambiguous situations.

**Without type annotation:**
```scala
val x = if (cond) Array(1) else Seq(2)
// Type: Array[Int] | Seq[Int]
```

**With type annotation:**
```scala
val x: Seq[Int] = if (cond) Array(1) else Seq(2)
// Type: Seq[Int] (Array converted to Seq)
```

### Our Strategy

We chose `Array[Expr]` as the target type because:
1. Most operations use arrays for efficiency
2. Conversion from `Seq` to `Array` is straightforward with `.toArray`
3. `Array` is the natural type for varargs in constructors like `Add(exprs: Array[Expr])`

## Files Fixed

1. **Add.scala**
   - Line 192: Added type annotation and `.toArray` conversion
   - Line 201: Removed unnecessary `.toArray`
   - Line 233: Changed Seq to Array with explicit type
   - Line 245: Removed unnecessary `.toArray`

2. **Mul.scala**
   - Line 169: Added explicit type parameter `Array[Expr]`

## Verification

To verify the fix works:

### Using SBT
```bash
cd /home/user/symbolicas
sbt compile
```

### Using Scala CLI
```bash
cd /home/user/symbolicas/src/main/scala
scala-cli compile symbolicas/*.scala
```

Expected output: **No compilation errors**

## Testing

Run existing tests to ensure functionality is preserved:

```bash
# Test configuration system
scala-cli test_config.sc

# Test cosine simplification
scala-cli test_cosine_simplification.sc

# Test Collatz expressions
scala-cli test.sc
```

## Summary

The compilation errors were caused by Scala 3's union type inference in conditional expressions. By adding explicit type annotations and ensuring consistent use of `Array[Expr]`, all type mismatches were resolved.

**Key Lesson:** In Scala 3, always add explicit type annotations when conditional expressions have different concrete types, even if they share a common supertype.

## Branch Information

**Branch:** `claude/fix-union-types-011CUqWKxzEzUXag6WBeTr7S`

**Commit:** `c6ed7e7` - Fix Scala 3 union type compilation errors in Add and Mul

**Pull Request:** https://github.com/angleto/symbolicas/pull/new/claude/fix-union-types-011CUqWKxzEzUXag6WBeTr7S

## Merge Instructions

To merge these fixes into v2.0:

```bash
git checkout v2.0
git merge claude/fix-union-types-011CUqWKxzEzUXag6WBeTr7S
sbt compile  # Verify compilation succeeds
sbt test     # Run tests if available
```

## Next Steps

1. **Merge this branch** into v2.0
2. **Compile and verify** no errors
3. **Run tests** to ensure functionality is intact
4. The v2.0 simplification system should now be fully operational!

## Related Documentation

- **COMPILATION_FIX.md** - Previous fix for missing imports
- **V2.0_RELEASE_NOTES.md** - Complete v2.0 feature overview
- **SIMPLIFICATION_CONFIG_GUIDE.md** - User guide for new features
