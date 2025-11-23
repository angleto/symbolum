import CollatzDescent.Collatz
import Mathlib.Data.Nat.Basic

/-!
# Descent for Collatz Sequences

This file defines the concept of descent for Collatz sequences
and related properties.

## Main definitions

* `descends n`: Proposition that n eventually becomes smaller under iteration
* `descentTime n`: The minimum number of steps until descent (noncomputable)

-/

namespace CollatzDescent

/-- A number descends if there exists k > 0 such that C^k(n) < n -/
def descends (n : ℕ) : Prop :=
  ∃ k : ℕ, k > 0 ∧ collatzIter k n < n

/-- Notation for descent -/
notation "↓" => descends

/-- A number converges to 1 if there exists k such that C^k(n) = 1 -/
def convergesToOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1

/-- The full Collatz conjecture: all positive integers converge to 1 -/
def CollatzConjecture : Prop :=
  ∀ n : ℕ, n > 0 → convergesToOne n

/-! ### Basic properties -/

/-- 1 trivially converges to 1 -/
lemma one_converges : convergesToOne 1 := by
  use 0
  rfl

/-- 2 converges to 1 in one step -/
lemma two_converges : convergesToOne 2 := by
  use 1
  exact collatz_two

/-- 4 converges to 1 in two steps -/
lemma four_converges : convergesToOne 4 := by
  use 2
  unfold collatzIter
  have : Even 4 := ⟨2, by omega⟩
  rw [collatz_even 4 (by omega) this]
  norm_num
  exact collatz_two

/-- If n converges and C(n) = m, then n converges in the same number of steps as m plus 1 -/
lemma converges_succ (n m : ℕ) (h_c : collatz n = m) (h_conv : convergesToOne m) :
    convergesToOne n := by
  obtain ⟨k, hk⟩ := h_conv
  use k + 1
  rw [collatzIter_succ, h_c, hk]

/-- If n descends to m < n and m converges, then n converges -/
lemma descends_and_converges_implies_converges (n m k : ℕ)
    (h_iter : collatzIter k n = m)
    (h_less : m < n)
    (h_conv : convergesToOne m) :
    convergesToOne n := by
  obtain ⟨j, hj⟩ := h_conv
  use k + j
  rw [collatzIter_add, h_iter, hj]

/-! ### Descent implies eventual decrease -/

/-- If n descends at step k, then C^k(n) < n -/
lemma descends_at_step (n k : ℕ) (h : k > 0 ∧ collatzIter k n < n) :
    descends n := by
  exact ⟨k, h⟩

/-- Descent is witnessed: if n descends, there exists an explicit witness -/
lemma descends_witness (n : ℕ) (h : descends n) :
    ∃ k > 0, collatzIter k n < n := h

end CollatzDescent
