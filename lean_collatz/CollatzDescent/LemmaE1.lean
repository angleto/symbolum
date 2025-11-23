import CollatzDescent.Collatz
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

/-!
# Lemma E.1: Immediate Exit from n ≡ 7 (mod 16)

This file proves that numbers n ≡ 7 (mod 16) immediately exit the n ≡ 7 (mod 8) class
in just one Collatz step.

## Main results

* `immediate_exit_mod16`: For n ≡ 7 (mod 16), C(n) ≡ 3 (mod 8)
* `immediate_exit_not_seven`: For n ≡ 7 (mod 16), C(n) ≢ 7 (mod 8)

## Significance

This lemma shows that exactly half of numbers in the n ≡ 7 (mod 8) class exit
immediately in one step. The other half (n ≡ 15 mod 16) are handled by Lemma E.2.

-/

namespace CollatzDescent

/-! ### Helper lemmas for n ≡ 7 (mod 16) -/

/-- If n ≡ 7 (mod 16), then n = 16k + 7 for some k -/
lemma exists_of_mod_sixteen_eq_seven (n : ℕ) (h : n % 16 = 7) :
    ∃ k : ℕ, n = 16 * k + 7 := by
  use n / 16
  omega

/-- For n = 16k + 7, compute C(n) -/
lemma collatz_sixteen_k_plus_seven (k : ℕ) :
    collatz (16 * k + 7) = 24 * k + 11 := by
  -- First show n is odd
  have h_odd : Odd (16 * k + 7) := by
    use 8 * k + 3
    ring
  -- Apply collatz formula for odd numbers
  rw [collatz_odd (16 * k + 7) h_odd]
  -- (3(16k+7)+1)/2 = (48k+22)/2 = 24k+11
  norm_num
  ring_nf
  omega

/-- For any k, 24k + 11 ≡ 3 (mod 8) -/
lemma twenty_four_k_plus_eleven_mod_eight (k : ℕ) :
    (24 * k + 11) % 8 = 3 := by
  -- 24k ≡ 0 (mod 8), so 24k + 11 ≡ 11 ≡ 3 (mod 8)
  have h1 : 24 * k % 8 = 0 := by
    have : 24 = 3 * 8 := by omega
    rw [this]
    ring_nf
    omega
  omega

/-! ### Main lemma: Immediate exit -/

/-- Lemma E.1 (Main): For n ≡ 7 (mod 16), C(n) ≡ 3 (mod 8)

    This proves immediate exit from the n ≡ 7 (mod 8) residue class.
-/
theorem immediate_exit_mod16 (n : ℕ)
    (h_odd : Odd n)
    (h_mod : n % 16 = 7) :
    collatz n % 8 = 3 := by
  -- Express n = 16k + 7
  obtain ⟨k, hk⟩ := exists_of_mod_sixteen_eq_seven n h_mod
  -- Compute C(n) = 24k + 11
  have hc : collatz n = 24 * k + 11 := by
    rw [hk]
    exact collatz_sixteen_k_plus_seven k
  -- Show 24k + 11 ≡ 3 (mod 8)
  rw [hc]
  exact twenty_four_k_plus_eleven_mod_eight k

/-- Corollary: For n ≡ 7 (mod 16), C(n) ≢ 7 (mod 8) -/
theorem immediate_exit_not_seven (n : ℕ)
    (h_odd : Odd n)
    (h_mod : n % 16 = 7) :
    collatz n % 8 ≠ 7 := by
  have h := immediate_exit_mod16 n h_odd h_mod
  omega

/-! ### Coverage analysis -/

/-- For n ≡ 7 (mod 8), either n ≡ 7 (mod 16) or n ≡ 15 (mod 16) -/
lemma mod_seven_eight_cases (n : ℕ) (h : n % 8 = 7) :
    n % 16 = 7 ∨ n % 16 = 15 := by
  omega

/-- Half of n ≡ 7 (mod 8) numbers exit immediately -/
theorem half_exit_immediately :
    ∀ n : ℕ, Odd n → n % 16 = 7 → collatz n % 8 = 3 :=
  immediate_exit_mod16

/-! ### Connection to Theorem E -/

/-- If n ≡ 7 (mod 16), then after one step we reach n' ≡ 3 (mod 8),
    which is handled by Theorem D.2 -/
theorem immediate_exit_to_mod3 (n : ℕ)
    (h_odd : Odd n)
    (h_mod : n % 16 = 7) :
    ∃ n' : ℕ, collatz n = n' ∧ n' % 8 = 3 := by
  use collatz n
  constructor
  · rfl
  · exact immediate_exit_mod16 n h_odd h_mod

/-! ### Computational verification examples -/

/-- Example: 7 ≡ 7 (mod 16) -/
example : (7 : ℕ) % 16 = 7 := by norm_num

/-- Example: C(7) = 11 -/
example : collatz 7 = 11 := by
  have h_odd : Odd 7 := by use 3; omega
  have : 7 = 16 * 0 + 7 := by omega
  rw [this]
  exact collatz_sixteen_k_plus_seven 0

/-- Example: 11 ≡ 3 (mod 8) -/
example : (11 : ℕ) % 8 = 3 := by norm_num

/-- Example: 23 ≡ 7 (mod 16) -/
example : (23 : ℕ) % 16 = 7 := by norm_num

/-- Example: C(23) = 35 -/
example : collatz 23 = 35 := by
  have h_odd : Odd 23 := by use 11; omega
  have : 23 = 16 * 1 + 7 := by omega
  rw [this]
  exact collatz_sixteen_k_plus_seven 1

/-- Example: 35 ≡ 3 (mod 8) -/
example : (35 : ℕ) % 8 = 3 := by norm_num

/-! ### Summary -/

/-- Lemma E.1 Summary: This lemma establishes that half of the n ≡ 7 (mod 8)
    numbers (those with n ≡ 7 mod 16) exit to n ≡ 3 (mod 8) in exactly one step.

    Combined with Lemma E.2 (which handles n ≡ 15 mod 16), this forms the
    foundation for Theorem E's proof that all n ≡ 7 (mod 8) eventually exit.
-/

end CollatzDescent
