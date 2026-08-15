import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open

/-- Iwaniec's retained absolute-error lower-sieve positivity certificate. -/
def formalizationClaim32758 (z y A B M X : ℝ) : Prop :=
  z > 1 ∧ z ^ 2 < y ∧ y < z ^ 4 ∧ A ≥ 0 ∧ B > 0 ∧ M > 0 ∧
    let s := Real.log y / Real.log z
    let f := 2 * Real.exp Real.eulerMascheroniConstant * (Real.log (s - 1) / s)
    (X / M) * (f - A / Real.log y) - B * y / (Real.log y) ^ 2 > 0

/-- The index-side condition in the exact lower Rosser support. -/
def rosserSupportIndexCondition (y z : ℝ) (k : ℕ) (p : Fin k → ℕ) : Prop :=
  (∀ i, Nat.Prime (p i)) ∧
  (∀ i j, i.val < j.val → p j < p i) ∧
  (∀ i : Fin k, i.val = 0 → z > p i) ∧
  (∀ j : ℕ, ∀ hj : 1 ≤ j, ∀ hjk : 2 * j ≤ k,
    (∏ i ∈ (Finset.univ.filter
        (fun i : Fin k => i.val < 2 * j - 1)), p i) *
        (p ⟨2 * j - 1, by omega⟩) ^ 3 < y)

/-- The lower Rosser support, with the displayed parameter choice `z=y^(1/s)`. -/
def exactLowerRosserSupport (y s : ℝ) : Set ℕ :=
  let z := Real.rpow y (1 / s)
  {d | ∃ k : ℕ, ∃ p : Fin k → ℕ,
    d = ∏ i, p i ∧ rosserSupportIndexCondition y z k p}

/-- The centered remainder in a shifted interval. -/
def rosserShiftRemainder (d : ℕ) (t N : ℝ) : ℝ :=
  (Int.floor ((t + N) / (d : ℝ)) : ℝ) -
    (Int.floor (t / (d : ℝ)) : ℝ) - N / (d : ℝ)

/-- Exact support and interval-remainder part of the lower Rosser claim. -/
def formalizationClaim32761 (y s : ℝ) : Prop :=
  y > 1 ∧ s ≥ 2 ∧
    (∀ d ∈ exactLowerRosserSupport y s, 0 < d ∧
      ∀ t N : ℝ, |rosserShiftRemainder d t N| < 1)

end MathlibPlus.Open
