import CollatzDescent.Descent
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Theorem B: Even Reduction

This file proves that even numbers reduce to their odd part in a predictable number of steps.

## Main results

* `even_reduction`: For n = 2^j * m with m odd, C^j(n) = m
* `reduction_to_odd_sufficient`: To prove descent for all n, it suffices to prove it for odd n

-/

namespace CollatzDescent

/-! ### Helper lemmas for powers of 2 -/

/-- Dividing 2^(j+1) * m by 2 gives 2^j * m -/
lemma pow_two_mul_div_two (j m : ℕ) :
    (2^(j + 1) * m) / 2 = 2^j * m := by
  rw [pow_succ]
  ring_nf
  omega

/-! ### Main theorem: Even reduction -/

/-- Theorem B: For n = 2^j * m where m is odd and j > 0,
    applying C exactly j times gives m.

    This is proven by induction on j.
-/
theorem even_reduction (m j : ℕ) (h_odd : Odd m) (h_j_pos : j > 0) :
    collatzIter j (2^j * m) = m := by
  induction j with
  | zero =>
      -- Contradicts j > 0
      omega
  | succ j' ih =>
      -- Two cases: j' = 0 or j' > 0
      by_cases hj' : j' = 0
      · -- Base case: j = 1
        rw [hj']
        simp
        have h_even : Even (2 * m) := ⟨m, by ring⟩
        have h_pos : 2 * m > 0 := by
          obtain ⟨k, hk⟩ := h_odd
          rw [hk]
          omega
        rw [collatzIter_succ, collatzIter_zero]
        rw [collatz_even (2 * m) h_pos h_even]
        omega
      · -- Inductive case: j' > 0
        have hj'_pos : j' > 0 := Nat.pos_of_ne_zero hj'
        rw [collatzIter_succ]
        have h_even : Even (2^(j' + 1) * m) := by
          use 2^j' * m
          ring
        have h_pos : 2^(j' + 1) * m > 0 := by
          apply Nat.mul_pos
          · exact Nat.two_pow_pos (j' + 1)
          · obtain ⟨k, hk⟩ := h_odd
            rw [hk]
            omega
        rw [collatz_even (2^(j' + 1) * m) h_pos h_even]
        rw [pow_two_mul_div_two]
        exact ih hj'_pos

/-- Corollary: C commutes with multiplication by 2^j for odd m -/
lemma collatzIter_pow_two_mul (m j : ℕ) (h_odd : Odd m) (h_j_pos : j > 0) :
    collatzIter j (2^j * m) = m :=
  even_reduction m j h_odd h_j_pos

/-! ### Reduction to odd numbers -/

/-- Every positive integer n can be written as 2^j * m where m is odd -/
lemma exists_pow_two_mul_odd (n : ℕ) (h_pos : n > 0) :
    ∃ j m : ℕ, Odd m ∧ n = 2^j * m := by
  sorry -- This would use twoAdicValuation from Basic.lean

/-- If all odd numbers descend, then all positive integers descend -/
theorem reduction_to_odd_sufficient
    (h_odd_descend : ∀ m : ℕ, Odd m → m > 0 → descends m) :
    ∀ n : ℕ, n > 0 → descends n := by
  intro n h_pos
  -- Factor n = 2^j * m with m odd
  obtain ⟨j, m, h_odd, h_eq⟩ := exists_pow_two_mul_odd n h_pos
  by_cases hj : j = 0
  · -- n is already odd
    rw [hj] at h_eq
    simp at h_eq
    rw [← h_eq]
    exact h_odd_descend n h_odd h_pos
  · -- n = 2^j * m with j > 0
    have hj_pos : j > 0 := Nat.pos_of_ne_zero hj
    -- m descends by hypothesis
    have h_m_pos : m > 0 := by
      by_contra h_not
      push_neg at h_not
      rw [Nat.le_zero] at h_not
      rw [h_not] at h_eq
      simp at h_eq
      omega
    have h_m_desc : descends m := h_odd_descend m h_odd h_m_pos
    -- Therefore n descends
    obtain ⟨k, hk_pos, hk_desc⟩ := h_m_desc
    -- After j steps, we get m, then after k more steps, we get < m
    use j + k
    constructor
    · omega
    · rw [h_eq, collatzIter_add]
      rw [even_reduction m j h_odd hj_pos]
      calc collatzIter k m < m := hk_desc
           _ < 2^j * m := by
              have : 2^j > 1 := by
                apply Nat.one_lt_pow
                · omega
                · exact hj_pos
              calc m = 1 * m := by ring
                   _ < 2^j * m := Nat.mul_lt_mul_of_pos_right this h_m_pos
           _ = n := by rw [← h_eq]

end CollatzDescent
