import Mathlib

namespace MathlibPlus.Open.Analysis.R0478

/-- Claim 25873: the fixed degree-five Boyd polynomial has a unique real
root outside the unit disk in `(6,7)`, and its ordering point exceeds six. -/
def orderingRootLocation_claim25873 : Prop :=
  let A : Polynomial ℝ :=
    Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X ^ 4 -
      Polynomial.C 6 * Polynomial.X ^ 3 - Polynomial.X ^ 2 +
      Polynomial.C 5 * Polynomial.X + Polynomial.C 4
  ∃ θ : ℝ,
    A.eval θ = 0 ∧ 1 < |θ| ∧ 6 < θ ∧ θ < 7 ∧
      (∀ y : ℝ, A.eval y = 0 → 1 < |y| → y = θ) ∧
      6 < θ + θ⁻¹

end MathlibPlus.Open.Analysis.R0478
