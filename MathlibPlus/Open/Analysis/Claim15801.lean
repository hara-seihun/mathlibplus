import Mathlib
import MathlibPlus.Open.Analysis.Claim15798

namespace MathlibPlus.Open.Analysis.Claim15801

noncomputable section

open MathlibPlus.Analysis.Claim15798

/-- The exact two-by-two matrix of the admitted folded-density kernel at the
ordered row and column points. -/
noncomputable def foldedDensityMatrix
    (x₀ x₁ u₀ u₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then foldedDensityKernel_claim15798 x₀ u₀
      else foldedDensityKernel_claim15798 x₀ u₁
    else if j = 0 then foldedDensityKernel_claim15798 x₁ u₀
      else foldedDensityKernel_claim15798 x₁ u₁

/-- Claim 15801: the concrete folded-density kernel is globally strictly
 totally positive of order two on the stated ordered domain. -/
def globalStrictTP2_claim15801 : Prop :=
  ∀ (x₀ x₁ u₀ u₁ : ℝ),
    0 < x₀ → x₀ < x₁ → u₀ < u₁ →
      Matrix.det (foldedDensityMatrix x₀ x₁ u₀ u₁) > 0

end

end MathlibPlus.Open.Analysis.Claim15801
