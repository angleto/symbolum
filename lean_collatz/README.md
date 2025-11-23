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
├── Basic.lean         - Fundamental definitions and helper lemmas
├── Collatz.lean       - Collatz function and iteration
├── Descent.lean       - Descent definition and properties
├── TheoremB.lean      - Even reduction theorem ✅
├── TheoremA.lean      - 2-step descent (TODO)
├── LemmaE1.lean       - Immediate exit (TODO)
├── LemmaE2.lean       - Persistence condition (TODO)
├── TheoremD2.lean     - Modular structure (TODO)
├── TheoremE.lean      - Forced exit (TODO)
└── TheoremG.lean      - Universal descent (TODO)
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
- [x] Theorem B: Even reduction (CollatzDescent/TheoremB.lean)
  - Proven by induction on j
  - Shows C^j(2^j · m) = m for odd m

### 🚧 In Progress

- [ ] Theorem A: 2-step descent for n ≡ 1 (mod 4)
  - Next priority
  - Should be straightforward

### 📋 Planned

- [ ] Lemmas E.1 and E.2 (modular structure)
- [ ] Theorem D.2 (n ≡ 3 mod 8 structure)
- [ ] Theorem E (forced exit) - **Most challenging**
- [ ] Theorem G (universal descent) - Final synthesis

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

### Phase 1: Easy Theorems (Weeks 1-3)
1. ✅ Theorem B (Even Reduction) - **DONE**
2. 🚧 Theorem A (2-Step Descent) - **IN PROGRESS**
3. 📋 Lemmas E.1, E.2

### Phase 2: Medium Theorems (Weeks 4-6)
4. 📋 Theorem D.2 (Modular structure)

### Phase 3: Hard Theorem (Weeks 7-10)
5. 📋 Theorem E (Forced exit) - **Most challenging**
   - May require computational proof for bounded range
   - Abstract pigeonhole argument for general case

### Phase 4: Synthesis (Weeks 11-12)
6. 📋 Theorem G (Universal descent)
   - Case analysis mod 8
   - Combine all previous theorems

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
