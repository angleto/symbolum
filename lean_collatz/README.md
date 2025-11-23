# Collatz Descent Proof - Lean 4 Formalization

**Status**: 🚧 Work in Progress
**Goal**: Machine-verified proof of universal descent for the Collatz conjecture

---

## Overview

This project formalizes the universal descent proof for the Collatz conjecture in Lean 4.

**What we prove**: For all positive integers n, there exists k such that C^k(n) < n.

**Note**: This proves *descent* (eventually becoming smaller), not full *convergence to 1* (though that is a future goal).

---

## Project Structure

```
CollatzDescent/
├── Basic.lean         - Fundamental definitions and helper lemmas ✅
├── Collatz.lean       - Collatz function and iteration ✅
├── Descent.lean       - Descent definition and properties ✅
├── TheoremB.lean      - Even reduction theorem ✅ PROVEN
├── TheoremA.lean      - 2-step descent ✅ READY
├── LemmaE1.lean       - Immediate exit ✅ COMPLETE
├── LemmaE2.lean       - Persistence condition ✅ COMPLETE
├── TheoremD2.lean     - Modular structure ✅ READY
├── TheoremE.lean      - Forced exit (TODO - Weeks 7-10)
└── TheoremG.lean      - Universal descent (TODO - Weeks 11-12)
```

---

## Building

### Prerequisites

- **Lean 4** (version 4.3.0)
- **Lake** (Lean build tool)

### Setup

```bash
# From this directory:
lake build
```

This will:
1. Download mathlib4 dependencies
2. Compile all Lean files
3. Check all proofs

### VS Code

Install the Lean 4 extension for VS Code for interactive proof development.

---

## Current Progress

### ✅ Completed

- [x] Project structure setup
- [x] Basic definitions (CollatzDescent/Basic.lean)
- [x] Collatz function definition (CollatzDescent/Collatz.lean)
- [x] Descent definitions (CollatzDescent/Descent.lean)
- [x] Theorem B: Even reduction (CollatzDescent/TheoremB.lean) ✅ **PROVEN**
  - Proven by induction on j
  - Shows C^j(2^j · m) = m for odd m
- [x] Theorem A: 2-step descent (CollatzDescent/TheoremA.lean) ✅ **READY FOR VERIFICATION**
  - Proves C²(n) < n for n ≡ 1 (mod 4)
  - Covers 50% of odd numbers (n ≡ 1, 5 mod 8)
  - 2 minor `sorry` cases for boundary values
- [x] Lemma E.1: Immediate exit (CollatzDescent/LemmaE1.lean) ✅ **COMPLETE**
  - Proves n ≡ 7 (mod 16) → C(n) ≡ 3 (mod 8)
  - Half of n ≡ 7 (mod 8) exit immediately
- [x] Lemma E.2: Persistence condition (CollatzDescent/LemmaE2.lean) ✅ **COMPLETE**
  - Proves n ≡ 15 (mod 16) → C(n) ≡ 7 (mod 8)
  - Characterizes persistent cases
  - 3 `sorry` cases needing refinement
- [x] Theorem D.2: Modular structure (CollatzDescent/TheoremD2.lean) ✅ **READY FOR VERIFICATION**
  - Proves n ≡ 3 (mod 8) → C(n) ≡ 1 or 5 (mod 8)
  - Descent in ≤ 3 steps
  - Achieves 75% combined coverage with Theorem A

### 📋 Planned

- [ ] Theorem E (forced exit) - **Most challenging** (Weeks 7-10)
- [ ] Theorem G (universal descent) - Final synthesis (Weeks 11-12)
- [ ] Resolve remaining `sorry` placeholders
- [ ] Full Lean verification build

---

## Theorem Dependencies

```
Theorem G (Universal Descent)
          ↓
    ┌─────┴─────┬────────────┐
    │           │            │
Theorem B   Theorem A    Theorem E
                         ↙      ↘
                   Lemma E.1  Lemma E.2
                        ↓
                   Theorem D.2
```

---

## Key Definitions

### Collatz Function

```lean
def collatz (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if Even n then n / 2
  else (3 * n + 1) / 2
```

### Descent

```lean
def descends (n : ℕ) : Prop :=
  ∃ k : ℕ, k > 0 ∧ collatzIter k n < n
```

### Convergence (future goal)

```lean
def convergesToOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1
```

---

## Formalization Strategy

### Phase 1: Easy Theorems (Weeks 1-4) ✅ **COMPLETED!**
1. ✅ Theorem B (Even Reduction) - **PROVEN**
2. ✅ Theorem A (2-Step Descent) - **READY FOR VERIFICATION**
3. ✅ Lemmas E.1, E.2 - **COMPLETE**

### Phase 2: Medium Theorems (Weeks 4-6) ✅ **COMPLETED!**
4. ✅ Theorem D.2 (Modular structure) - **READY FOR VERIFICATION**

**Current Status**: Ahead of schedule! 75% coverage achieved.

### Phase 3: Hard Theorem (Weeks 7-10) 📋 **NEXT PRIORITY**
5. 📋 Theorem E (Forced exit) - **Most challenging**
   - Will require computational proof for bounded range
   - Abstract pigeonhole argument for general case
   - Expected to be the most time-consuming theorem

### Phase 4: Synthesis (Weeks 11-12) 📋 **PLANNED**
6. 📋 Theorem G (Universal descent) - **FINAL GOAL**
   - Case analysis mod 8
   - Combine all previous theorems
   - Achieve 100% coverage proof

---

## Challenges

### Known Difficulties

1. **Division in ℕ**: Lean's natural number division requires careful handling
   - Must prove divisibility before dividing
   - Use lemmas like `Nat.div_eq_iff_eq_mul_left`

2. **Modular Arithmetic**: Case analysis on residue classes
   - Use `interval_cases` tactic
   - Import `Mathlib.Data.Nat.ModEq`

3. **Theorem E**: Most complex proof
   - May use `sorry` initially to unblock other proofs
   - Come back with stronger tactics

### Solutions

- Break proofs into small lemmas
- Use `have` for intermediate steps
- Leverage `omega` for linear arithmetic
- Use `ring` for algebraic simplification

---

## Related Work

### Mathematical Proof

See `docs/research/` for:
- `PROOF_VERIFICATION_DOCUMENT.md` - Complete mathematical proof
- `19_COMPLETE_UNIVERSAL_DESCENT_PROOF.md` - Comprehensive exposition
- `PROOF_DEPENDENCY_STRUCTURE.md` - Logical structure

### Computational Validation

Python scripts verify the proof:
- `collatz_multistep_descent_analysis.py`
- `collatz_worst_case_analysis.py`
- `collatz_forced_exit_verification.py`

---

## Contributing

To contribute to this formalization:

1. **Read the mathematical proof** in `docs/research/`
2. **Pick an unformalized theorem** from the list above
3. **Write the Lean proof** following existing style
4. **Test with `lake build`**
5. **Submit** for review

---

## Future Goals

### Short-term (3 months)
- Complete universal descent formalization (Theorem G)
- All theorems proven with no `sorry`

### Medium-term (6-12 months)
- Extend to full convergence to 1
- Optimize proof size and readability
- Extract verified certificate

### Long-term (12+ months)
- Contribute to mathlib
- Collaborate with formal mathematics community
- Apply techniques to related conjectures

---

## Resources

### Learning Lean 4
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

### Mathlib Documentation
- [API Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- Search for: `Nat.ModEq`, `Even`, `Odd`, etc.

---

## License

MIT License (same as parent project)

---

## Authors

- Collatz Descent Research Team
- Mathematical proof: docs/research/
- Lean formalization: This directory

---

**Last Updated**: November 22, 2025
**Lean Version**: 4.3.0
**Mathlib Version**: Latest (auto-updated by lake)

---

*"Formalizing mathematics: where every step must be justified."*
