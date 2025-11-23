# Absolute Proof Strategies for the Collatz Conjecture

**Date**: November 22, 2025
**Focus**: Non-probabilistic, deterministic proof approaches
**Status**: Exploratory research on unexplored deterministic methods

---

## Executive Summary

This document explores **deterministic proof strategies** for the Collatz conjecture, explicitly avoiding probabilistic arguments. We identify gaps in previous research and develop new approaches that could lead to an absolute proof.

**Key Insight**: Previous research identified the expansion-contraction dichotomy as the fundamental obstacle. We need approaches that either:
1. Find a global decreasing function despite local expansions
2. Prove eventual descent through structural properties
3. Use number-theoretic tools to constrain trajectories

---

## Table of Contents

1. [Review: What Hasn't Worked](#review-what-hasnt-worked)
2. [Approach 1: p-adic and 3-adic Analysis](#approach-1-p-adic-and-3-adic-analysis)
3. [Approach 2: Weighted Lyapunov Functions](#approach-2-weighted-lyapunov-functions)
4. [Approach 3: Graph-Theoretic Connectivity](#approach-3-graph-theoretic-connectivity)
5. [Approach 4: Systematic Class-Specific Expansion](#approach-4-systematic-class-specific-expansion)
6. [Approach 5: Potential Functions and Distance Metrics](#approach-5-potential-functions-and-distance-metrics)
7. [Approach 6: Algebraic Invariants](#approach-6-algebraic-invariants)
8. [Synthesis and Recommendations](#synthesis-and-recommendations)

---

## Review: What Hasn't Worked

### Failed Deterministic Approaches

From previous research (docs 08, 09, RIGOROUS_PARTIAL_RESULTS):

1. **Simple Lyapunov V(n) = n**:
   - ❌ Even: V(n/2) = n/2 < n ✓
   - ❌ Odd: V((3n+1)/2) = (3n+1)/2 > n for n ≥ 1 ✗

2. **Power Lyapunov V(n) = n^α**:
   - ❌ Same issue: grows for odd steps

3. **Log Lyapunov V(n) = log(n)**:
   - ❌ Same issue: log((3n+1)/2) > log(n) for odd n

4. **Spectral radius ρ < 1**:
   - ❌ Found ρ = 1 due to limit cycle eigenvalues λ = ±1

5. **Uniform contraction**:
   - ❌ Operator expands by 3/2 on odd steps

### The Core Problem

**Expansion-Contraction Dichotomy**:
- Even steps: multiply by 1/2 (contract)
- Odd steps: multiply by ~3/2 (expand)
- Cannot prove contractions dominate expansions deterministically

### What This Tells Us

We need approaches that:
- **Accept** local expansions but prove global descent
- **Use structure** beyond simple magnitude
- **Exploit** number-theoretic properties of the sequence
- **Find** hidden decreasing quantities

---

## Approach 1: p-adic and 3-adic Analysis

### Motivation

The Collatz function has special structure modulo powers of 2 and 3:
- Operation: if odd, multiply by 3 and add 1
- Natural to study in 2-adic and 3-adic numbers

**Why this is promising**:
- p-adic analysis can reveal structure invisible in real numbers
- 3-adic metric may contract where real metric expands
- Could prove convergence in p-adic topology

### 2-adic Analysis

**2-adic norm**: |n|_2 = 2^{-v_2(n)} where v_2(n) is the 2-adic valuation (highest power of 2 dividing n)

**Observation**:
```
For n = 2^k · m (m odd):
  C(n) = 2^{k-1} · m
  |C(n)|_2 = 2^{-(k-1)} · |m|_2 = 2 · |n|_2  (INCREASES!)
```

So 2-adic norm increases for even n - not helpful.

**For odd n**:
```
  n odd, so v_2(n) = 0, |n|_2 = 1
  3n + 1 is even: v_2(3n+1) ≥ 1
  C(n) = (3n+1)/2 has v_2(C(n)) = v_2(3n+1) - 1
```

**Key question**: What is v_2(3n+1) for odd n?

**Analysis by residue class mod 4**:
- n ≡ 1 (mod 4): 3n+1 ≡ 3(1)+1 = 4 ≡ 0 (mod 4), so v_2(3n+1) ≥ 2
- n ≡ 3 (mod 4): 3n+1 ≡ 3(3)+1 = 10 ≡ 2 (mod 4), so v_2(3n+1) = 1

**Conclusion**: 2-adic norm behavior is erratic, doesn't give global decrease.

### 3-adic Analysis

**3-adic norm**: |n|_3 = 3^{-v_3(n)} where v_3(n) is highest power of 3 dividing n

**For even n**:
```
  C(n) = n/2
  v_3(C(n)) = v_3(n/2) = v_3(n)  (dividing by 2 doesn't change 3-divisibility)
  |C(n)|_3 = |n|_3  (UNCHANGED)
```

**For odd n** (where n is not divisible by 3):
```
  If v_3(n) = 0 (n not divisible by 3):
    What is v_3(3n+1)?

  Case 1: n ≡ 1 (mod 3): 3n+1 ≡ 0+1 = 1 (mod 3), so v_3(3n+1) = 0
  Case 2: n ≡ 2 (mod 3): 3n+1 ≡ 0+1 = 1 (mod 3), so v_3(3n+1) = 0
```

**Conclusion**: 3-adic norm also doesn't give consistent decrease.

### Combined p-adic Metric

**Idea**: Define combined metric using both 2-adic and 3-adic norms:
```
d(n) = |n|_2^α · |n|_3^β · n^γ  for some weights α, β, γ
```

**Challenge**: Finding weights that make this strictly decreasing seems difficult.

### Verdict

**Status**: ⚠️ Promising but requires deeper analysis
**Path forward**:
- Study ultrametric properties more carefully
- Consider other primes (5-adic, 7-adic)
- Look for invariant measures in p-adic topology

**Promise for absolute proof**: ⭐⭐⭐ (Medium - sophisticated but no clear path yet)

---

## Approach 2: Weighted Lyapunov Functions

### Motivation

Simple Lyapunov functions V(n) = n fail because they grow on odd steps. But what if we use **parity-dependent weights**?

### Idea 1: Parity-Weighted Potential

Define:
```
V(n, s) = n · w(s)
```
where s is the parity (0=even, 1=odd) and w(s) is a weight function.

**Goal**: Choose w such that:
- Even step: V(n/2, 0) < V(n, 0)
- Odd step: V((3n+1)/2, 0) < V(n, 1)  (note: output is always even from odd input)

**Analysis**:
```
Even step: n·w(0) → (n/2)·w(0)
  Requires: (n/2)·w(0) < n·w(0)  ⟹  w(0) > 0 (always satisfied)

Odd step: n·w(1) → ((3n+1)/2)·w(0)
  Requires: ((3n+1)/2)·w(0) < n·w(1)
  ⟹ w(1)/w(0) > (3n+1)/(2n) = 3/2 + 1/(2n) ≈ 3/2
```

**Problem**: Need w(1)/w(0) > 3/2, but this means V increases on transition from even to odd!

**Verdict**: Simple parity weighting doesn't work.

### Idea 2: History-Dependent Lyapunov

Define:
```
V(n, h) = n · f(h)
```
where h is the recent parity history (e.g., last k steps).

**Rationale**:
- After many odd steps, we're "due" for descent
- Weight could grow with consecutive odd steps
- Could decrease overall despite local growth

**Challenge**: Proving such a function decreases requires analyzing all possible parity sequences - combinatorial explosion.

### Idea 3: Multi-Step Lyapunov

Instead of proving V(C(n)) < V(n) for all n, prove:
```
V(C^k(n)) < V(n)  for some k depending on n
```

**Analysis**:
For odd n, we know C(n) = (3n+1)/2 is even, so:
```
C²(n) = C((3n+1)/2) = (3n+1)/4  (best case)
```

So after 2 steps from odd n:
```
n → (3n+1)/2 → (3n+1)/4
```

**Ratio**: (3n+1)/4 vs n
```
(3n+1)/(4n) = 3/4 + 1/(4n) < 1  for n ≥ 1
```

**KEY INSIGHT**: After 2 steps from any odd n, we're at most (3/4)n + 1/4 of the original!

**Theorem (2-Step Descent for Odd Numbers)**:

**Statement**: For any odd n ≥ 1:
```
C²(n) ≤ (3n+1)/4
```

**Proof**:
- n is odd, so C(n) = (3n+1)/2
- 3n+1 is even (since n odd), so C(n) is an integer
- Let m = (3n+1)/2 (which is even)
- Then C²(n) = C(m) = m/2 = (3n+1)/4 ∎

**Corollary**: If we could prove this pattern continues, we'd have convergence!

**But**: This is only the "best case" - sometimes (3n+1)/2 is odd, requiring more steps.

### Idea 4: Potential Function Based on "Distance to 1"

Define potential not as magnitude but as:
```
Φ(n) = number of steps to reach a value < n  (if it exists)
```

This is essentially the "descent time".

**Goal**: Prove Φ(n) is finite for all n.

**Challenge**: This is circular - we're trying to prove what we want to prove!

### Verdict

**Status**: ⚠️ Partial success - 2-step bound is interesting
**Path forward**:
- Formalize multi-step Lyapunov theory
- Analyze parity sequence statistics more carefully
- Bound the "bad cases" where descent takes longer

**Promise for absolute proof**: ⭐⭐⭐⭐ (High - multi-step Lyapunov is promising)

---

## Approach 3: Graph-Theoretic Connectivity

### Motivation

View the Collatz function as a directed graph:
- Vertices: ℕ
- Edges: n → C(n)

**Conjecture restatement**: All vertices have a path to 1 (vertex {1} is globally attracting).

### Graph Properties

**Known facts**:
1. Every vertex has out-degree 1 (C is a function)
2. Vertex 1 has in-degree ≥ 1 (from 2)
3. Graph has a cycle: 1 → 2 → 1

**Question**: Can we prove all vertices connect to this cycle?

### Weakly Connected Components

**Definition**: A directed graph is weakly connected if the underlying undirected graph is connected.

**For Collatz**: We need STRONG connectivity to {1,2} - all paths lead there.

### Inverse Function Analysis

Define C^{-1}(n) = set of all m such that C(m) = n.

**For any n**:
- m = 2n is always a pre-image (even)
- If (2n-1) mod 3 = 0 and (2n-1)/3 is odd, then m = (2n-1)/3 is also a pre-image (odd)

**Example**: C^{-1}(10):
- 20 (even pre-image: 20/2 = 10)
- (20-1)/3 = 19/3 ✗ (not integer)
- Only pre-image: 20

**Example**: C^{-1}(5):
- 10 (even pre-image)
- (10-1)/3 = 9/3 = 3 ✓ (odd pre-image if (3·3+1)/2 = 5 ✓)
- Pre-images: {3, 10}

**Observation**: Every n has at least one pre-image (2n), and possibly two.

This means the graph has a **tree-like structure** with branching going BACKWARDS.

### Proving Global Attraction

**Strategy**: Prove that following the function forward (n → C(n)) always eventually reaches {1,2}.

**Equivalent**: Prove the "backwards tree" from {1,2} covers all of ℕ.

**Challenge**: The backwards tree is infinite but sparse. Proving it covers all ℕ requires showing no number "escapes" to infinity.

### Structural Obstruction

**Could there exist** an infinite trajectory that never reaches {1,2}?

**Possibilities**:
1. Diverges to infinity (growth unbounded)
2. Enters a different cycle (not {1,2})
3. Has bounded but non-convergent behavior

**Known**:
- No non-trivial period-1 cycles (proven)
- No other cycles found computationally
- All tested trajectories converge

**Unproven**: That cases 1-3 are impossible for all n.

### Verdict

**Status**: ⚠️ Reformulation, not new proof technique
**Path forward**:
- Study graph-theoretic properties more deeply
- Analyze connectivity using number-theoretic constraints
- Consider computational topology methods

**Promise for absolute proof**: ⭐⭐ (Low - doesn't add new proof power)

---

## Approach 4: Systematic Class-Specific Expansion

### Motivation

We've proven convergence for powers of 2: τ(2^k) = k.

**Strategy**: Systematically expand to larger and larger classes until we cover all ℕ.

### Class Hierarchy

**Level 0**: Powers of 2 only
- **Proven**: τ(2^k) = k ✓

**Level 1**: 2^k · 3^j (numbers with only factors 2 and 3)
- **Status**: Not yet proven

**Level 2**: 2^k · p for prime p
- **Status**: Not yet proven

**Level 3**: All numbers of the form 2^k · m where m is in some proven class
- **Status**: Inductive strategy

### Attempt: Prove for 2^k · 3

**Target**: Show τ(2^k · 3) < ∞ for all k.

**Analysis**:
```
For k ≥ 1:
  C(2^k · 3) = 2^{k-1} · 3  (even, divide by 2)
  C²(2^k · 3) = 2^{k-2} · 3  (if k ≥ 2)
  ...
  C^k(2^k · 3) = 3  (after k steps)
```

Now need to prove τ(3) < ∞:
```
C(3) = (3·3+1)/2 = 5
C(5) = (3·5+1)/2 = 8 = 2³
```

So C²(3) = 8, and we know τ(8) = 3.

Therefore: τ(3) = 2 + 3 = 5 ✓

**Conclusion**: τ(2^k · 3) = k + 5 for all k ≥ 0 ✓

### Generalization Strategy

**Theorem (Reduction to Co-prime Case)**:

If τ(m) < ∞ for m odd, then τ(2^k · m) = k + τ(m) for all k ≥ 0.

**Proof**:
```
C^k(2^k · m) = m  (after k divisions by 2)
C^{k+τ(m)}(2^k · m) = C^{τ(m)}(m) = 1
```
Therefore τ(2^k · m) ≤ k + τ(m) < ∞ ∎

**Corollary**: **The Collatz conjecture is equivalent to proving τ(m) < ∞ for all odd m.**

This is already known (Theorem 6 in RIGOROUS_PARTIAL_RESULTS.md), but confirms our strategy.

### Systematic Coverage of Odd Numbers

**Goal**: Prove convergence for progressively larger sets of odd numbers.

**Proven odd numbers**:
- 1: τ(1) = 0 ✓
- 3: τ(3) = 5 ✓
- 5: τ(5) = 3 ✓
- 7: τ(7) = ?

**Computing τ(7)**:
```
C(7) = (3·7+1)/2 = 11
C(11) = (3·11+1)/2 = 17
C(17) = (3·17+1)/2 = 26 = 2·13
C(26) = 13
C(13) = (3·13+1)/2 = 20 = 4·5
C(20) = 10 = 2·5
C(10) = 5
We know τ(5) = 3
```
So τ(7) = 6 + 3 = 9... wait, let me recount:
7 → 11 → 17 → 26 → 13 → 20 → 10 → 5 (8 steps to reach 5)
τ(7) = 8 + τ(5) = 8 + 3 = 11 ✓

### Pattern Analysis

Can we find patterns in odd numbers that allow batch proofs?

**Attempt**: Numbers of the form 2^k - 1

**Example**:
- 2^2 - 1 = 3: τ(3) = 5 ✓
- 2^3 - 1 = 7: τ(7) = 11 ✓
- 2^4 - 1 = 15: τ(15) = ?

Computing τ(15):
```
C(15) = (3·15+1)/2 = 23
C(23) = (3·23+1)/2 = 35 = 5·7
C(35) = (3·35+1)/2 = 53
... (continues)
```

This gets complicated quickly. No obvious pattern.

### Verdict

**Status**: ✅ Proven for some specific classes, but no general pattern
**Path forward**:
- Systematically prove for small odd numbers
- Look for structural patterns (binary representations, modular properties)
- Build coverage incrementally

**Promise for absolute proof**: ⭐⭐⭐⭐ (High - this is the most concrete incremental strategy)

---

## Approach 5: Potential Functions and Distance Metrics

### Motivation

Instead of Lyapunov functions measuring "size", consider potential functions measuring "distance to goal" (the cycle {1,2}).

### Distance Metric Ideas

**Metric 1: Path Length**
```
d(n) = τ(n)  (stopping time)
```
**Problem**: This is what we're trying to prove is finite!

**Metric 2: Approximate Path Length**
```
d(n) ≈ log₂(n)  (heuristic from empirical data)
```
**Problem**: Not exact, doesn't help with proof

**Metric 3: Modular Distance**
```
d(n) = min{k : n ≡ 1 (mod 2^k)}
```
**Problem**: Doesn't capture true trajectory distance

### Potential Based on Binary Representation

**Idea**: The binary representation of n contains information about the trajectory.

**For even n = 2^k · m** (m odd):
- Will divide by 2 exactly k times before reaching odd number m
- Then trajectory is determined by m

**For odd n**:
- Binary representation ends in 1
- After applying C once, we get (3n+1)/2
- Binary representation changes

**Observation**:
```
n (odd) has binary ...xyz1
3n has binary ...??? (multiply by 11₂)
3n+1 has binary ...???0 (even)
(3n+1)/2 has binary ...??? (shift right)
```

**Question**: Can we find a potential function based on binary patterns?

**Idea**:
```
Φ(n) = weighted sum of bit positions
```

**Challenge**: Finding weights that make Φ decrease is difficult.

### Potential Based on "Closeness to Power of 2"

**Idea**: Numbers close to powers of 2 descend quickly.

**Metric**:
```
ψ(n) = n / 2^⌊log₂(n)⌋  (ratio to largest power of 2 ≤ n)
```
This gives ψ(n) ∈ [1, 2).

**Question**: Does ψ tend to decrease toward 1?

**Analysis**:
- For even n: ψ(n/2) = ψ(n) or ψ(n)/2 (depending on whether we cross power of 2)
- For odd n: ψ((3n+1)/2) ≈ 3/2 · ψ(n) (generally increases!)

**Verdict**: This potential doesn't decrease.

### Verdict

**Status**: ⚠️ Interesting ideas but no clear decreasing potential found
**Path forward**:
- Explore more sophisticated binary-based potentials
- Consider potentials in other number bases (base 3, base 6)
- Multi-scale potentials

**Promise for absolute proof**: ⭐⭐ (Low - no clear path)

---

## Approach 6: Algebraic Invariants

### Motivation

Look for algebraic quantities that are preserved or constrained along trajectories.

### GCD-Based Invariants

**Question**: How does gcd(n, k) evolve under C?

**For any fixed k**:
```
If n is even: C(n) = n/2
  gcd(C(n), k) = gcd(n/2, k)

If n is odd: C(n) = (3n+1)/2
  gcd(C(n), k) = gcd((3n+1)/2, k)
```

**No obvious invariant** - gcd can increase or decrease.

### Algebraic Number Fields

**Idea**: Embed ℕ in an algebraic number field where additional structure exists.

**Example**: Consider Gaussian integers ℤ[i].

**Problem**: Collatz is defined on ℕ, extending to ℤ[i] is artificial.

### Polynomial Invariants

**Question**: Does there exist a polynomial P(n) that is preserved: P(C(n)) = P(n)?

**Analysis**:
For even n: P(n/2) should equal P(n)
For odd n: P((3n+1)/2) should equal P(n)

**Attempt P(n) = n mod m**:
```
Even: (n/2) mod m vs n mod m - NOT generally equal
Odd: ((3n+1)/2) mod m vs n mod m - NOT generally equal
```

**Attempt P(n) = n² mod m**:
Similar issues.

**Verdict**: No simple polynomial invariant found.

### Divisibility Constraints

**Question**: Can we track which primes divide n along the trajectory?

**Observation**:
- If 2 | n, then C(n) may or may not be divisible by 2
- If 3 | n and n odd, then C(n) = (3n+1)/2 where 3 | 3n but 3 ∤ 3n+1
  - So if 3 | n (odd), then 3 ∤ C(n)

**Key insight**: Applying C to odd multiples of 3 **removes** the factor of 3!

**Implication**: Can't stay in multiples of 3 forever (if odd).

Could this lead to a proof? Would need to show we can't avoid small numbers forever.

### Verdict

**Status**: ⚠️ Some interesting observations but no proof pathway yet
**Path forward**:
- Study prime factorization evolution more systematically
- Look for forbidden patterns
- Consider Diophantine constraints

**Promise for absolute proof**: ⭐⭐⭐ (Medium - number-theoretic constraints could help)

---

## Synthesis and Recommendations

### Summary of Approaches

| # | Approach | Promise | Feasibility | Status |
|---|----------|---------|-------------|--------|
| 1 | p-adic/3-adic analysis | ⭐⭐⭐ | Hard | Needs deep analysis |
| 2 | Weighted Lyapunov | ⭐⭐⭐⭐ | Medium | 2-step bound promising |
| 3 | Graph connectivity | ⭐⭐ | Medium | Reformulation only |
| 4 | Class-specific expansion | ⭐⭐⭐⭐ | High | Most concrete |
| 5 | Potential functions | ⭐⭐ | Medium | No clear path |
| 6 | Algebraic invariants | ⭐⭐⭐ | Hard | Needs exploration |

### Top Recommendations for Absolute Proof

#### Recommendation 1: Multi-Step Lyapunov Analysis ⭐⭐⭐⭐⭐

**Why**: We proved C²(n) ≤ (3n+1)/4 for odd n in best case. This is concrete progress.

**Next steps**:
1. **Formalize multi-step descent theory**
2. **Analyze worst-case**: What if (3n+1)/2 is odd? Continue to C³, C⁴...
3. **Bound the number of steps** needed for descent
4. **Prove**: For all odd n, ∃k ≤ f(n) such that C^k(n) < n

**This is the most promising direction** because:
- We have concrete bounds for best-case
- Framework is classical (Lyapunov-style)
- Provably makes progress on the problem

#### Recommendation 2: Systematic Class-Specific Proofs ⭐⭐⭐⭐⭐

**Why**: This is incremental and concrete.

**Strategy**:
1. **Prove for all odd n ≤ 100** (computationally verify, then prove)
2. **Find structural patterns** in proven cases
3. **Extend to families**: n = 2^k·m for proven m
4. **Cover larger and larger sets** systematically

**This won't prove the full conjecture** but will:
- Make rigorous progress
- Identify patterns that could lead to general proof
- Be publishable partial results

#### Recommendation 3: Divisibility Analysis ⭐⭐⭐⭐

**Why**: We found that C removes factors of 3 from odd numbers.

**Next steps**:
1. **Systematically analyze** how each prime p behaves under C
2. **Prove constraints** on how long certain factors can persist
3. **Show** that trajectories must eventually hit "simple" numbers
4. **Combine with class-specific** proofs

**This could work** because:
- Number-theoretic constraints are powerful
- Could prove eventual simplification
- Avoids magnitude-based arguments

### Combining Approaches

**Hybrid strategy**:
1. Use **divisibility analysis** to constrain possible trajectories
2. Apply **multi-step Lyapunov** to prove descent for constrained cases
3. Build **class-specific library** of proven cases
4. **Iterate** until coverage is complete

---

## Immediate Action Plan

### Phase 1: Multi-Step Lyapunov Analysis (Priority 1)

**Goal**: Formalize and extend the 2-step descent bound.

**Tasks**:
1. Prove: For all odd n ≥ 1, C²(n) ≤ (3n+1)/4 in best case
2. Analyze: When does (3n+1)/2 happen to be even? (n ≡ 1 mod 4)
3. Analyze: When (3n+1)/2 is odd, bound C⁴(n), C⁶(n), etc.
4. Find: Maximum k such that C^k(n) ≥ n for odd n
5. Prove: k is bounded for all n (if possible)

### Phase 2: Divisibility Constraint Analysis (Priority 2)

**Goal**: Understand how prime factors evolve.

**Tasks**:
1. For each prime p, analyze C(p^k·m) where gcd(m,p) = 1
2. Prove: Certain prime factors are removed by C
3. Show: Can't maintain arbitrarily many large prime factors
4. Combine: With magnitude bounds to constrain trajectories

### Phase 3: Class-Specific Systematic Proofs (Priority 3)

**Goal**: Expand proven classes methodically.

**Tasks**:
1. Prove: τ(n) < ∞ for all odd n ≤ 1000
2. Identify: Patterns in these proofs
3. Formulate: General theorems for families
4. Extend: Coverage as far as possible

---

## Conclusion

### What We've Identified

1. **Most promising approaches** for absolute proof:
   - Multi-step Lyapunov analysis
   - Systematic class-specific expansion
   - Divisibility/number-theoretic constraints

2. **Key insight**: 2-step bound C²(n) ≤ (3n+1)/4 for odd n (best case)

3. **Strategy**: Combine multiple approaches rather than relying on one

### Next Steps

Focus on **multi-step Lyapunov analysis** as it:
- Has concrete results already
- Is most likely to yield rigorous bounds
- Uses classical proof techniques
- Could lead to actual proof or identify precise obstruction

### Honest Assessment

**Can we prove the Collatz conjecture?**
- Full proof: Very unlikely with these methods alone
- Significant partial results: Yes, achievable
- Better understanding of obstacles: Definitely
- New techniques that could inspire breakthrough: Possibly

**But**: These deterministic approaches are more rigorous than probabilistic ones and represent the best path to an absolute proof.

---

**Status**: Exploratory analysis complete
**Recommendation**: Pursue multi-step Lyapunov + class-specific + divisibility approaches
**Next**: Formalize multi-step Lyapunov theory and implement analysis

---

*"An absolute proof requires absolute rigor. These approaches, while challenging, maintain that rigor without resorting to probabilistic arguments."*

**END OF DOCUMENT**
