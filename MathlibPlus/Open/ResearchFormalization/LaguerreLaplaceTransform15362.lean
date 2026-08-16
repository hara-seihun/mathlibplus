import Mathlib
import MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.LaguerreLaplaceTransform15362

noncomputable section

/-- The Laplace transform of the parameter-two generalized Laguerre polynomial. -/
noncomputable def laguerreLaplace (δ : ℝ) (d : ℕ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-δ * t) *
      MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360.laguerreTwo d t

/-- Claim 15362: the exact Laplace transform for every degree and positive real parameter. -/
def exactLaplaceTransform_claim15362 : Prop :=
  ∀ d : ℕ, ∀ δ : ℝ, 0 < δ →
    laguerreLaplace δ d =
      (d : ℝ) + 2 - δ + δ * (-(1 - δ) / δ) ^ (d + 2)

end

end MathlibPlus.Open.ResearchFormalization.LaguerreLaplaceTransform15362
