import CollatzDescent.Basic
import Mathlib.Data.Nat.Basic

/-!
# The Collatz Function

This file defines the Collatz function and its iteration.

## Main definitions

* `collatz n`: The Collatz function C(n)
* `collatzIter k n`: k-fold iteration C^k(n)

## Implementation notes

We use the simplified form C(n) = (3n+1)/2 for odd n, which combines
the traditional 3n+1 step with the guaranteed subsequent division by 2.

-/

namespace CollatzDescent

/-- The Collatz function.
    * For even n: C(n) = n/2
    * For odd n: C(n) = (3n+1)/2

    We define C(0) = 0 for completeness, though the Collatz conjecture
    is typically stated for positive integers.
-/
def collatz (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if Even n then n / 2
  else (3 * n + 1) / 2

/-- Notation for Collatz function -/
notation "C" => collatz

/-- k-fold iteration of the Collatz function -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatz (collatzIter k n)

/-- Notation for iterated Collatz: C^[k](n) means apply C k times to n -/
notation "C^[" k "]" => collatzIter k

/-! ### Basic properties of collatz -/

/-- Collatz of zero is zero -/
lemma collatz_zero : collatz 0 = 0 := by
  unfold collatz
  simp

/-- For even n > 0, C(n) = n/2 -/
lemma collatz_even (n : ℕ) (h_pos : n > 0) (h_even : Even n) :
    collatz n = n / 2 := by
  unfold collatz
  simp [h_pos.ne', h_even]

/-- For odd n, C(n) = (3n+1)/2 -/
lemma collatz_odd (n : ℕ) (h_odd : Odd n) :
    collatz n = (3 * n + 1) / 2 := by
  obtain ⟨k, hk⟩ := h_odd
  unfold collatz
  have h_ne_zero : n ≠ 0 := by
    intro h_eq
    rw [h_eq] at hk
    omega
  have h_not_even : ¬Even n := Nat.odd_iff_not_even.mp h_odd
  simp [h_ne_zero, h_not_even]

/-- C(1) = 2 -/
lemma collatz_one : collatz 1 = 2 := by
  have : Odd 1 := ⟨0, by omega⟩
  rw [collatz_odd 1 this]
  norm_num

/-- C(2) = 1 -/
lemma collatz_two : collatz 2 = 1 := by
  have : Even 2 := ⟨1, by omega⟩
  rw [collatz_even 2 (by omega) this]
  norm_num

/-- For odd n > 0, C(n) is well-defined (3n+1 is divisible by 2) -/
lemma collatz_odd_well_defined (n : ℕ) (h_odd : Odd n) :
    2 * collatz n = 3 * n + 1 := by
  rw [collatz_odd n h_odd]
  exact three_n_plus_one_div_two_eq n h_odd

/-! ### Properties of collatzIter -/

/-- C^[0](n) = n -/
lemma collatzIter_zero (n : ℕ) : collatzIter 0 n = n := rfl

/-- C^[k+1](n) = C(C^[k](n)) -/
lemma collatzIter_succ (k n : ℕ) : collatzIter (k + 1) n = collatz (collatzIter k n) := rfl

/-- Iteration is composition -/
lemma collatzIter_add (j k n : ℕ) :
    collatzIter (j + k) n = collatzIter k (collatzIter j n) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Nat.succ_add, collatzIter_succ, collatzIter_succ, ih]

end CollatzDescent
