import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-!
Formalization of admitted claim 25196.  `n` and `r` are natural numbers, so
`binom(n - 2, 2) ≥ 2r` is represented by `Nat.choose (n - 2) 2 ≥ 2 * r`.
The rational gap lemma retains the displayed `(n-2)(n-7)/2` lower bound.
The final theorem makes the source's "remaining band" explicit as
`5 ≤ n < 7` and `3 ≤ r ≤ n - 2`; without those bounds the three listed pairs
would not be exhaustive.
-/

/-- The large-order capacity bound from claim 25196. -/
theorem chain_capacity_large_claim25196 {n r : ℕ}
    (hn : 7 ≤ n) (hr : r ≤ n - 2) :
    (n - 2).choose 2 ≥ 2 * r := by
  rw [Nat.choose_two_right]
  change 2 * r ≤ (n - 2) * (n - 2 - 1) / 2
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  have hn3 : 4 ≤ n - 3 := by omega
  have hprod : (n - 2) * 4 ≤ (n - 2) * (n - 2 - 1) := by
    have hshift : n - 3 = n - 2 - 1 := by omega
    rw [← hshift]
    exact Nat.mul_le_mul_left (n - 2) hn3
  have hr4 : 4 * r ≤ 4 * (n - 2) := Nat.mul_le_mul_left 4 hr
  calc
    2 * r * 2 = 4 * r := by ring
    _ ≤ 4 * (n - 2) := hr4
    _ = (n - 2) * 4 := by ring
    _ ≤ (n - 2) * (n - 2 - 1) := hprod

/-- The displayed quadratic gap is nonnegative in the large-order range. -/
theorem chain_capacity_gap_claim25196 {n r : ℕ}
    (hn : 7 ≤ n) (hr : r ≤ n - 2) :
    ((Nat.choose (n - 2) 2 : ℚ) - 2 * (r : ℚ) ≥
        (((n - 2 : ℕ) : ℚ) * ((n - 7 : ℕ) : ℚ)) / 2) ∧
      0 ≤ (((n - 2 : ℕ) : ℚ) * ((n - 7 : ℕ) : ℚ)) / 2 := by
  rw [Nat.cast_choose_two]
  have hn2 : 2 ≤ n := by omega
  have hn7 : 7 ≤ n := hn
  rw [Nat.cast_sub hn2, Nat.cast_sub hn7]
  norm_num
  have hnQ : (7 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hrQ : (r : ℚ) ≤ (n : ℚ) - 2 := by
    calc
      (r : ℚ) ≤ ((n - 2 : ℕ) : ℚ) := by exact_mod_cast hr
      _ = (n : ℚ) - 2 := by rw [Nat.cast_sub hn2]; norm_num
  have hnonneg : 0 ≤ (n : ℚ) - 7 := by linarith
  have hnonneg2 : 0 ≤ (n : ℚ) - 2 := by linarith
  constructor
  · nlinarith
  · positivity

/-- Below order seven, under the source's remaining-band hypotheses, the only
possibilities are `(5,3)`, `(6,3)`, and `(6,4)`; the middle one is equality and
the other two fail the capacity bound. -/
theorem chain_capacity_small_claim25196 {n r : ℕ}
    (hn : 5 ≤ n) (hn' : n < 7) (hr : 3 ≤ r) (hr' : r ≤ n - 2) :
    (n = 5 ∧ r = 3 ∧ ¬ ((n - 2).choose 2 ≥ 2 * r)) ∨
    (n = 6 ∧ r = 3 ∧ (n - 2).choose 2 ≥ 2 * r ∧
      (n - 2).choose 2 = 2 * r) ∨
    (n = 6 ∧ r = 4 ∧ ¬ ((n - 2).choose 2 ≥ 2 * r)) := by
  have hn_cases : n = 5 ∨ n = 6 := by omega
  rcases hn_cases with rfl | rfl
  · have hr_cases : r = 3 := by omega
    subst r
    left
    norm_num [Nat.choose]
  · have hr_cases : r = 3 ∨ r = 4 := by omega
    rcases hr_cases with rfl | rfl
    · right
      left
      norm_num [Nat.choose]
    · right
      right
      norm_num [Nat.choose]

end MathlibPlus.Combinatorics
