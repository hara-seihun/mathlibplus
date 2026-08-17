import Mathlib

namespace MathlibPlus.Open.Analysis.RapidityBatch

noncomputable section

/-- Claim 19384: the finite-rapidity off-diagonal shortfall is exactly the
positive quantity q sech²(ξ), written as q / cosh²(ξ). -/
def offDiagonalRapidityShortfall_claim19384 : Prop :=
  ∀ (q ξ : ℝ), 0 < q →
    q * (1 + (Real.tanh ξ) ^ 2) =
      2 * q - q / (Real.cosh ξ) ^ 2 ∧
    0 < q / (Real.cosh ξ) ^ 2

end

end MathlibPlus.Open.Analysis.RapidityBatch
