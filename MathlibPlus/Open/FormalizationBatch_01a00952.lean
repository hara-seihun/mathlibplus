import Mathlib

namespace MathlibPlus.Open.FormalizationBatch_01a00952

/-- Boundary value of the affine completion at the specified point. -/
def claim13631 : Prop :=
  ∀ (t : ℕ → ℝ) (H T : ℝ → ℝ),
    Summable (fun n : ℕ => t n * (1 / 4 : ℝ) ^ n) →
    T (1 / 4 : ℝ) =
      ∑' n : ℕ, t n * (1 / 4 : ℝ) ^ n →
    (∀ z : ℝ,
      H z = (1 / 2 : ℝ) + (z - (1 / 4 : ℝ)) * T z) →
    H (1 / 4 : ℝ) = (1 / 2 : ℝ)

/-- Fixed-depth regular variation gives a limiting multiplier ratio of one. -/
def claim13643 : Prop :=
  ∀ (j : ℕ) (D m : ℕ → ℕ → ℝ)
      (exponent : ℕ → ℝ) (slow : ℕ → ℕ → ℝ),
    1 ≤ j →
    (∀ r : ℕ, (r = j ∨ r = j - 1) →
      (∀ᶠ n in Filter.atTop, D n r ≠ 0) ∧
      (∃ error : ℕ → ℝ,
        Filter.Tendsto error Filter.atTop (nhds 0) ∧
        (∀ᶠ n in Filter.atTop,
          D n r =
            Real.rpow (n : ℝ) (-exponent r) *
              slow r n * (1 + error n)) ∧
        Filter.Tendsto (fun n : ℕ => slow r (n - 1) / slow r n)
          Filter.atTop (nhds 1))) →
    (∀ᶠ n in Filter.atTop, m n 0 ≠ 0) →
    (∀ᶠ n in Filter.atTop,
      m n j =
        m n 0 *
          (D n j * D (n - 2) (j - 1) /
            (D (n - 1) j * D (n - 1) (j - 1)))) →
    Filter.Tendsto (fun n : ℕ => m n j / m n 0)
      Filter.atTop (nhds 1)

end MathlibPlus.Open.FormalizationBatch_01a00952
