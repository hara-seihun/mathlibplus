import Mathlib

namespace MathlibPlus.Open.Analysis.LambertBatch

private noncomputable def principalLambertW (x : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x}

private noncomputable def lambertProfile (j : ℕ) : ℝ :=
  (4 * (j : ℝ))⁻¹ * principalLambertW ((j : ℝ) / (2 * Real.pi))

/-- Uniform equivalence of the logarithmic gauge and Lambert profile. -/
def uniform_equivalence_logarithmic_gauge_lambert_profile
    (α₀ α₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n q : ℕ,
      N ≤ n →
      1 ≤ q →
      α₀ ≤ (q : ℝ) / (n : ℝ) →
      (q : ℝ) / (n : ℝ) ≤ α₁ →
      |Real.log ((Real.log (n : ℝ) / (8 * (q : ℝ))) /
          lambertProfile (2 * q - 1))| < ε

end MathlibPlus.Open.Analysis.LambertBatch
