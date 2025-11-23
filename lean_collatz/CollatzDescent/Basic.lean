import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

/-!
# Basic Definitions for Collatz Descent

This file contains fundamental definitions and lemmas used throughout
the formalization of the universal descent proof.

## Main definitions

* `twoAdicValuation n`: The largest power of 2 dividing n
* Helper lemmas for modular arithmetic

-/

namespace CollatzDescent

/-- The 2-adic valuation: largest k such that 2^k divides n.
    Returns 0 for n = 0. -/
def twoAdicValuation (n : ℕ) : ℕ :=
  if n = 0 then 0
  else Nat.find (Nat.exists_eq_pow_mul_of_le_two (by decide : 2 ≤ 2) n)

/-- Alternative characterization: n = 2^(v₂(n)) * m where m is odd -/
lemma twoAdicValuation_spec (n : ℕ) (hn : n ≠ 0) :
    ∃ m : ℕ, Odd m ∧ n = 2^(twoAdicValuation n) * m := by
  sorry

/-- Helper: check if n ≡ a (mod 8) -/
def modEightEq (n a : ℕ) : Prop := n % 8 = a % 8

notation n " ≡₈ " a => modEightEq n a

/-- Helper lemmas for modular arithmetic -/
lemma odd_iff_mod_two_eq_one {n : ℕ} : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    omega
  · intro h
    use n / 2
    omega

lemma even_iff_mod_two_eq_zero {n : ℕ} : Even n ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    omega
  · intro h
    use n / 2
    omega

/-- For odd n, 3n+1 is even -/
lemma three_n_plus_one_even (n : ℕ) (h : Odd n) : Even (3 * n + 1) := by
  obtain ⟨k, hk⟩ := h
  use 3 * k + 2
  rw [hk]
  ring

/-- For odd n, (3n+1)/2 is well-defined in ℕ -/
lemma three_n_plus_one_div_two_eq (n : ℕ) (h : Odd n) :
    2 * ((3 * n + 1) / 2) = 3 * n + 1 := by
  have : Even (3 * n + 1) := three_n_plus_one_even n h
  obtain ⟨k, hk⟩ := this
  rw [hk]
  omega

end CollatzDescent
