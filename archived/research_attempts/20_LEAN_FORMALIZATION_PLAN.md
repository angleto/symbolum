# Lean Formalization Plan: Universal Descent Proof

**Date**: November 22, 2025
**Goal**: Formalize the universal descent proof in Lean 4
**Status**: Planning phase

---

## Table of Contents

1. [Overview](#overview)
2. [Lean Project Structure](#lean-project-structure)
3. [Formalization Strategy](#formalization-strategy)
4. [Definition Hierarchy](#definition-hierarchy)
5. [Theorem Formalization Order](#theorem-formalization-order)
6. [Expected Challenges](#expected-challenges)
7. [Timeline and Milestones](#timeline-and-milestones)

---

## Overview

### Why Lean?

**Advantages**:
1. **Machine-verified correctness** - No gaps, no errors
2. **Mathlib integration** - Access to extensive mathematical library
3. **Modern proof assistant** - Lean 4 has excellent tooling
4. **Community** - Active and growing
5. **Readability** - Lean proofs are relatively readable

**Goal**: Formalize Theorems B, A, D.2, E, G in Lean 4 to obtain machine-verified proof of universal descent.

---

## Lean Project Structure

### Directory Layout

```
lean_collatz/
├── lakefile.lean                 # Lake build configuration
├── lean-toolchain                # Lean version specification
├── CollatzDescent/
│   ├── Basic.lean               # Core definitions and basic lemmas
│   ├── Collatz.lean             # Collatz function definition
│   ├── Descent.lean             # Descent definition and properties
│   ├── TheoremB.lean            # Even reduction theorem
│   ├── TheoremA.lean            # 2-step descent for n ≡ 1 (mod 4)
│   ├── LemmaE1.lean             # Immediate exit for n ≡ 7 (mod 16)
│   ├── LemmaE2.lean             # Persistence condition
│   ├── TheoremD2.lean           # Modular structure for n ≡ 3 (mod 8)
│   ├── TheoremE.lean            # Forced exit for n ≡ 7 (mod 8)
│   ├── TheoremG.lean            # Universal descent (main result)
│   └── Computational.lean       # Computational validation
└── README.md
```

### Dependencies

**Lean version**: 4.3.0 or later
**Mathlib dependencies**:
- `Mathlib.Data.Nat.Basic` - Natural number basics
- `Mathlib.Data.Nat.Prime` - Number theory
- `Mathlib.Data.Nat.ModEq` - Modular arithmetic
- `Mathlib.Tactic.Ring` - Ring normalization
- `Mathlib.Tactic.Omega` - Linear arithmetic
- `Mathlib.Algebra.BigOperators` - For iterations

---

## Formalization Strategy

### Phase 1: Core Definitions (Week 1)

**File: `CollatzDescent/Basic.lean`**

Define fundamental concepts:

```lean
-- 2-adic valuation
def twoAdicValuation (n : ℕ) : ℕ := sorry

-- Modular residue helpers
def modEight (n : ℕ) : Fin 8 := ⟨n % 8, by omega⟩

-- Odd number predicate
def isOdd (n : ℕ) : Prop := ¬Even n
```

**File: `CollatzDescent/Collatz.lean`**

Define Collatz function:

```lean
/-- The Collatz function.
    For even n: C(n) = n/2
    For odd n: C(n) = (3n+1)/2
-/
def collatz (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if Even n then n / 2
  else (3 * n + 1) / 2

notation "C" => collatz

/-- k-fold iteration of Collatz function -/
def collatzIter (k : ℕ) (n : ℕ) : ℕ :=
  match k with
  | 0 => n
  | k + 1 => collatz (collatzIter k n)

notation "C^[" k "]" => collatzIter k
```

**File: `CollatzDescent/Descent.lean`**

Define descent:

```lean
/-- n descends if there exists k such that C^k(n) < n -/
def descends (n : ℕ) : Prop :=
  ∃ k : ℕ, k > 0 ∧ collatzIter k n < n

/-- Descent time: minimum k where descent occurs -/
noncomputable def descentTime (n : ℕ) : ℕ :=
  Nat.find (descends_witness n)

notation "τ" => descentTime
```

---

### Phase 2: Even Reduction (Week 1-2)

**File: `CollatzDescent/TheoremB.lean`**

Formalize Theorem B:

```lean
/-- Theorem B: Even numbers reduce to their odd part -/
theorem even_reduction (n : ℕ) (m : ℕ) (j : ℕ)
    (h1 : n = 2^j * m)
    (h2 : Odd m)
    (h3 : j > 0) :
    collatzIter j n = m := by
  -- Proof by induction on j
  induction j with
  | zero =>
      -- Contradiction: j > 0
      omega
  | succ j' ih =>
      -- Base case j=1 and inductive step
      sorry

/-- Corollary: Descent time for even numbers -/
theorem descent_time_even (n m : ℕ) (j : ℕ)
    (h1 : n = 2^j * m)
    (h2 : Odd m)
    (h3 : j > 0) :
    descentTime n = j + descentTime m := by
  sorry
```

**Estimated difficulty**: Medium
**Key tactics**: `induction`, `omega`, `ring`, `simp`

---

### Phase 3: Theorem A (Week 2-3)

**File: `CollatzDescent/TheoremA.lean`**

Formalize 2-step descent:

```lean
/-- Theorem A: 2-step descent for n ≡ 1 (mod 4) -/
theorem two_step_descent (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 4 = 1)
    (h3 : n ≥ 5) :
    collatzIter 2 n = (3 * n + 1) / 4 ∧
    collatzIter 2 n < n := by
  -- Extract k from n = 4k + 1
  obtain ⟨k, hk⟩ := Nat.eq_add_of_sub_eq h2
  -- Compute C(n)
  have c1 : collatz n = 6 * k + 2 := by
    unfold collatz
    -- Algebraic manipulation
    sorry
  -- Compute C²(n)
  have c2 : collatzIter 2 n = 3 * k + 1 := by
    unfold collatzIter
    rw [c1]
    -- C(6k+2) = (6k+2)/2 = 3k+1
    sorry
  -- Prove inequality
  constructor
  · -- Formula part
    sorry
  · -- Inequality part: 3k+1 < 4k+1
    omega

/-- Corollary: Covers n ≡ 1, 5 (mod 8) -/
theorem two_step_descent_mod8 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 1 ∨ n % 8 = 5)
    (h3 : n ≥ 5) :
    descends n := by
  -- n ≡ 1 or 5 (mod 8) implies n ≡ 1 (mod 4)
  have : n % 4 = 1 := by
    cases h2 <;> omega
  obtain ⟨_, h⟩ := two_step_descent n h1 this h3
  use 2
  exact ⟨by omega, h⟩
```

**Estimated difficulty**: Medium
**Key tactics**: `omega`, `ring`, `obtain`, `cases`

---

### Phase 4: Lemmas E.1 and E.2 (Week 3-4)

**File: `CollatzDescent/LemmaE1.lean`**

```lean
/-- Lemma E.1: Immediate exit for n ≡ 7 (mod 16) -/
lemma immediate_exit_mod16 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 16 = 7) :
    collatz n % 8 = 3 := by
  -- n = 16k + 7
  obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mp h2
  -- C(n) = 24k + 11
  have : collatz n = 24 * k + 11 := by
    unfold collatz
    sorry
  -- 24k + 11 ≡ 3 (mod 8) for all k
  sorry
```

**File: `CollatzDescent/LemmaE2.lean`**

```lean
/-- Lemma E.2: Persistence condition -/
lemma persistence_condition (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 7) :
    (collatz n % 8 = 7) ↔ (n % 16 = 15) := by
  constructor
  · -- Forward direction
    intro hc
    -- If C(n) ≡ 7 (mod 8) and n ≡ 7 (mod 8)
    -- then by Lemma E.1, n ≢ 7 (mod 16)
    -- so n ≡ 15 (mod 16)
    sorry
  · -- Backward direction
    intro hn
    -- n = 16k + 15 implies C(n) = 24k + 23 ≡ 7 (mod 8)
    sorry
```

**Estimated difficulty**: Medium-Hard
**Key tactics**: `omega`, `ring`, modular arithmetic lemmas

---

### Phase 5: Theorem D.2 (Week 4-5)

**File: `CollatzDescent/TheoremD2.lean`**

```lean
/-- Theorem D.2: Modular structure for n ≡ 3 (mod 8) -/
theorem modular_structure_mod3 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 3) :
    collatz n % 8 = 1 ∨ collatz n % 8 = 5 := by
  -- n = 8k + 3
  obtain ⟨k, hk⟩ := sorry
  -- C(n) = 12k + 5
  have : collatz n = 12 * k + 5 := by sorry
  -- Case split on k even/odd
  by_cases hk_even : Even k
  · -- k even: 12k + 5 ≡ 5 (mod 8)
    right
    sorry
  · -- k odd: 12k + 5 ≡ 1 (mod 8)
    left
    sorry

/-- Corollary: Descent for n ≡ 3 (mod 8) -/
theorem descent_mod3 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 3)
    (h3 : n ≥ 3) :
    descends n := by
  -- C(n) ≡ 1 or 5 (mod 8), both ≡ 1 (mod 4)
  have h_struct := modular_structure_mod3 n h1 h2
  -- Apply Theorem A to C(n)
  sorry
```

**Estimated difficulty**: Medium
**Key tactics**: `by_cases`, `omega`, `ring`

---

### Phase 6: Theorem E (Week 5-8) - **MOST CHALLENGING**

**File: `CollatzDescent/TheoremE.lean`**

```lean
/-- Theorem E: Forced exit from n ≡ 7 (mod 8)
    Note: This is the hardest theorem to formalize
-/
theorem forced_exit_mod7 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 7)
    (h3 : n ≥ 7) :
    ∃ k : ℕ, k > 0 ∧ k ≤ 2 * (Nat.log2 n) + 5 ∧
    (collatzIter k n) % 8 = 3 := by
  -- This will require substantial work
  -- Strategy:
  -- 1. Prove half exit immediately (Lemma E.1)
  -- 2. For persistent cases, show bounded exit
  -- 3. Use strong induction on n
  sorry

/-- Corollary: Descent bound for n ≡ 7 (mod 8) -/
theorem descent_bound_mod7 (n : ℕ)
    (h1 : Odd n)
    (h2 : n % 8 = 7)
    (h3 : n ≥ 7) :
    ∃ k : ℕ, k > 0 ∧ k ≤ 2 * (Nat.log2 n) + 8 ∧
    collatzIter k n < n := by
  -- Get forced exit from Theorem E
  obtain ⟨k1, hk1_pos, hk1_bound, hk1_exit⟩ := forced_exit_mod7 n h1 h2 h3
  -- Apply Theorem D.2 to get descent
  sorry
```

**Estimated difficulty**: **Very Hard**
**Key challenges**:
- Formalizing pigeonhole argument
- Bounding iteration count
- Modular induction

**Strategy for Theorem E**:
1. First prove computationally for small n (n < 10,000)
2. Use `decide` tactic for finite cases
3. For general case, may need to:
   - Develop custom tactics
   - Use auxiliary lemmas about modular patterns
   - Formalize the pigeonhole argument carefully

---

### Phase 7: Theorem G (Week 8-9)

**File: `CollatzDescent/TheoremG.lean`**

```lean
/-- Theorem G: Universal Descent - MAIN RESULT -/
theorem universal_descent :
    ∀ n : ℕ, n > 0 → descends n := by
  intro n hn
  -- Case split: even or odd
  by_cases h_even : Even n
  · -- Even case: use Theorem B to reduce to odd
    sorry
  · -- Odd case: classify by n % 8
    have h_odd : Odd n := h_even
    interval_cases (n % 8)
    · -- n ≡ 0 (mod 8): impossible (n is odd)
      omega
    · -- n ≡ 1 (mod 8): use Theorem A
      exact two_step_descent_mod8 n h_odd (Or.inl rfl) sorry
    · -- n ≡ 2 (mod 8): impossible (n is odd)
      omega
    · -- n ≡ 3 (mod 8): use Theorem D.2
      exact descent_mod3 n h_odd rfl sorry
    · -- n ≡ 4 (mod 8): impossible (n is odd)
      omega
    · -- n ≡ 5 (mod 8): use Theorem A
      exact two_step_descent_mod8 n h_odd (Or.inr rfl) sorry
    · -- n ≡ 6 (mod 8): impossible (n is odd)
      omega
    · -- n ≡ 7 (mod 8): use Theorem E
      obtain ⟨k, hk⟩ := descent_bound_mod7 n h_odd rfl sorry
      exact ⟨k, hk⟩
```

**Estimated difficulty**: Medium (assuming prerequisites are done)
**Key tactics**: `by_cases`, `interval_cases`, `omega`

---

## Definition Hierarchy

### Level 0: Lean/Mathlib Basics
- `ℕ` - Natural numbers
- `Even`, `Odd` - Parity
- `%` - Modulo operator
- `/` - Division

### Level 1: Custom Definitions
- `twoAdicValuation` - Power of 2 in factorization
- `collatz` - Collatz function
- `collatzIter` - k-fold iteration

### Level 2: Descent Concepts
- `descends` - Existence of descent
- `descentTime` - Minimum descent step

### Level 3: Theorems
- Theorem B → Theorem A → Theorem D.2
- Lemmas E.1, E.2 → Theorem E
- All above → Theorem G

---

## Expected Challenges

### Challenge 1: Division in ℕ

**Issue**: Lean's natural number division is not quite the same as mathematical division.

**Solution**:
- Prove divisibility first: `∃ q, n = 2 * q`
- Use `Nat.div_eq_iff_eq_mul_left` and similar lemmas

Example:
```lean
-- For odd n, prove 3n+1 is even before dividing
lemma three_n_plus_one_even (n : ℕ) (h : Odd n) :
    Even (3 * n + 1) := by
  sorry

-- Then division is well-defined
```

### Challenge 2: Modular Arithmetic

**Issue**: Modular reasoning requires careful case analysis.

**Solution**:
- Use `Mathlib.Data.Nat.ModEq`
- Import lemmas like `Nat.add_mod`, `Nat.mul_mod`
- Use `omega` tactic for linear arithmetic

### Challenge 3: Theorem E Formalization

**Issue**: Pigeonhole argument and bound derivation are complex.

**Potential approaches**:

**Option 1: Computational proof for bounded range**
```lean
-- Prove for all n ≤ N by computation
theorem forced_exit_bounded (n : ℕ)
    (h : n ≤ 100000) : ... := by
  interval_cases n
  all_goals decide
```

**Option 2: Abstract pigeonhole principle**
```lean
-- Formalize general pigeonhole argument
-- Apply to Collatz setting
```

**Option 3: Admit Theorem E initially**
```lean
-- Use axiom to complete other proofs
axiom theorem_e : ...

-- Come back to prove it later
```

### Challenge 4: Proof Engineering

**Issue**: Proofs can become very long and unreadable.

**Best practices**:
- Break proofs into small lemmas
- Use `have` for intermediate steps
- Name hypotheses clearly
- Use `·` for focused subgoals

---

## Timeline and Milestones

### Week 1-2: Setup and Foundations
- [ ] Set up Lean project structure
- [ ] Define Collatz function
- [ ] Define descent
- [ ] Prove basic properties (C is well-defined, etc.)
- [ ] Formalize Theorem B

**Milestone 1**: Even reduction proven in Lean

### Week 3-4: Base Cases
- [ ] Formalize Theorem A
- [ ] Formalize Lemma E.1
- [ ] Formalize Lemma E.2
- [ ] Prove 50% coverage (Theorem A)

**Milestone 2**: Half of odd numbers proven in Lean

### Week 5-6: Modular Structure
- [ ] Formalize Theorem D.2
- [ ] Prove 75% coverage

**Milestone 3**: Three-quarters proven in Lean

### Week 7-10: Theorem E (Critical Phase)
- [ ] Develop formalization strategy
- [ ] Prove computationally for n ≤ 10,000
- [ ] Work on general proof
- [ ] May need to develop custom tactics

**Milestone 4**: Theorem E formalized (hardest part)

### Week 11-12: Synthesis
- [ ] Formalize Theorem G
- [ ] Clean up proofs
- [ ] Documentation
- [ ] Extract certificate

**Milestone 5**: Universal descent proven in Lean! 🎉

### Total: ~12 weeks (3 months)

---

## Success Criteria

**Minimum viable formalization**:
- [ ] All definitions formalized
- [ ] Theorem B proven
- [ ] Theorem A proven
- [ ] Theorem D.2 proven
- [ ] Theorem E proven (possibly with some admits)
- [ ] Theorem G proven

**Gold standard**:
- [ ] All theorems fully proven (no axioms/admits)
- [ ] Computational validation formalized
- [ ] Bounds are tight
- [ ] Code is well-documented
- [ ] Proofs are readable

---

## Resources

### Learning Lean 4
- **Theorem Proving in Lean 4**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Mathematics in Lean**: https://leanprover-community.github.io/mathematics_in_lean/
- **Lean Zulip Chat**: https://leanprover.zulipchat.com/

### Similar Formalizations
- **Odd Goldbach in Lean**: Study their proof engineering
- **Fermat's Little Theorem**: Good example of modular arithmetic
- **Prime Number Theorem**: Example of sophisticated proof

### Mathlib Documentation
- Search for: `Nat.ModEq`, `Nat.Prime`, `Even`, `Odd`
- Study existing number theory proofs

---

## Next Steps

1. **Create Lean project**:
   ```bash
   lake new CollatzDescent
   cd CollatzDescent
   ```

2. **Set up lakefile.lean**:
   ```lean
   require mathlib from git
     "https://github.com/leanprover-community/mathlib4.git"
   ```

3. **Create Basic.lean** with initial definitions

4. **Start with Theorem B** (easiest proof)

5. **Iterate and refine**

---

## Conclusion

Formalizing the universal descent proof in Lean is an ambitious but achievable goal. The main challenges are:

1. **Theorem E formalization** - Most complex, may take several weeks
2. **Modular arithmetic** - Requires careful handling
3. **Proof engineering** - Keeping proofs manageable

**Estimated total effort**: 200-300 hours over 3 months

**Value**:
- Machine-verified proof (no gaps, no errors)
- Foundation for further formalization (full convergence)
- Contribution to formal mathematics
- Learning experience with Lean 4

Let's begin! 🚀

---

**Status**: Plan complete, ready to begin implementation
**Next file**: Create lakefile.lean and start with Basic.lean
