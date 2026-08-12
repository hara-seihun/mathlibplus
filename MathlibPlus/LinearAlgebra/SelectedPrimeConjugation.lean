import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.LinearAlgebra.Claim2290

/- The source writes `c^(-1/4)` without specifying a real-power convention.
   We use `Real.rpow`, and expose the required `c > 1` domain explicitly. -/
noncomputable def selectedPrimeRealLinearMap (c : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ -
    (Real.rpow c (-1 / 4 : ℝ)) • Complex.conjCLE.toContinuousLinearMap

end MathlibPlus.LinearAlgebra.Claim2290

namespace MathlibPlus.Open.LinearAlgebra

/-- Claim 2290, with the inverse norm represented by the operator norm of a
continuous real-linear equivalence. -/
def selectedPrimeRealLinearMapClaim2290 : Prop :=
  ∀ c : ℝ, 1 < c →
    ∃ e : ℂ ≃L[ℝ] ℂ,
      e.toContinuousLinearMap =
          MathlibPlus.LinearAlgebra.Claim2290.selectedPrimeRealLinearMap c ∧
        ‖e.symm.toContinuousLinearMap‖ ≤
          (1 - Real.rpow c (-1 / 4 : ℝ))⁻¹

end MathlibPlus.Open.LinearAlgebra
