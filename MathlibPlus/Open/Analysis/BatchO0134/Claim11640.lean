import Mathlib

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11640

open scoped BigOperators

/-- Compact-source energy for a bounded, compactly supported real source. -/
def compactSourceEnergy
    (E : ℕ → ℝ → (ℝ → ℝ) → ℝ) : Prop :=
  ∀ (m : ℕ) (σ : ℝ) (C : ℝ → ℝ),
    Bornology.IsBounded (Set.range C) →
    HasCompactSupport C →
    let K : ℕ → ℝ → ℝ → ℝ := fun m t u =>
      (-1 : ℝ) ^ m *
        iteratedDeriv m (fun s : ℝ =>
          Real.exp (-(u ^ 2) / (4 * s)) /
            (2 * Real.sqrt (Real.pi * s))) t
    E m σ C =
      (Real.exp (2 * (m : ℝ)) /
        (m : ℝ) ^ (2 * (m : ℝ) + 2 * σ)) *
        ∫ t in Set.Ioi (0 : ℝ),
          t ^ (2 * (m : ℝ) + 2 * σ - 1) *
            (abs (∫ u in Set.Ioi (0 : ℝ),
              C u * deriv (fun v : ℝ => K m t v) u)) ^ 2

end MathlibPlus.Open.Analysis.BatchO0134.Claim11640
