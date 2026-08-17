import Mathlib
import MathlibPlus.Open.Analysis.Claim15798
import MathlibPlus.Open.Analysis.Claim15801

namespace MathlibPlus.Open.Analysis.CompleteRankThreeFoldedDensity15802

open MathlibPlus.Analysis.Claim15798

noncomputable section

/-- The ordered three-by-three matrix of the admitted folded-density kernel. -/
def foldedDensityMatrix3
    (x₀ x₁ x₂ u₀ u₁ u₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    foldedDensityKernel_claim15798
      (if i = 0 then x₀ else if i = 1 then x₁ else x₂)
      (if j = 0 then u₀ else if j = 1 then u₁ else u₂)

/-- Claim 15802: the ordered rank-three folded-density determinant is
strictly positive on the stated ordered real domain. -/
def completeRankThreeFoldedDensity_claim15802 : Prop :=
  ∀ (x₀ x₁ x₂ u₀ u₁ u₂ : ℝ),
    0 < x₀ →
    x₀ < x₁ →
    x₁ < x₂ →
    u₀ < u₁ →
    u₁ < u₂ →
    Matrix.det (foldedDensityMatrix3 x₀ x₁ x₂ u₀ u₁ u₂) > 0

end

end MathlibPlus.Open.Analysis.CompleteRankThreeFoldedDensity15802
