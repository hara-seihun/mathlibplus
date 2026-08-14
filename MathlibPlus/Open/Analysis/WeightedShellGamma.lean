import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory

/-- The closed formula for every integer-shape Gamma moment in the weighted-shell tower. -/
noncomputable def weighted_shell_gamma_moment : Prop :=
  ∀ (m j ell : ℕ),
    1 ≤ m →
    let ρ : ℝ := 2 * Real.pi * (m : ℝ) ^ 2 - (1 : ℝ) / 2
    let ν : ℕ := 2 * j + 1
    ρ > 2 * (ell : ℝ) →
      (∫ u in Set.Ioi (0 : ℝ),
        (Real.exp (2 * u) - 1 - 2 * u) ^ ell *
          (ρ ^ ν / (Nat.factorial (ν - 1) : ℝ)) *
          u ^ (ν - 1) * Real.exp (-ρ * u)) =
        ∑ q ∈ Finset.range (ell + 1),
          (Nat.choose ell q : ℝ) * (-1 : ℝ) ^ (ell - q) *
            ∑ r ∈ Finset.range (ell - q + 1),
              (Nat.choose (ell - q) r : ℝ) * (2 : ℝ) ^ r *
                (Nat.ascFactorial ν r : ℝ) * ρ ^ ν /
                  (ρ - 2 * (q : ℝ)) ^ (ν + r)

end MathlibPlus.Open.Analysis
