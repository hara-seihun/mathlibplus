import MathlibPlus.Open.Analysis.CompletedThetaPositiveDefinite11936

namespace MathlibPlus.Open.Analysis.CompletedThetaAutocorrelation

noncomputable section

open MathlibPlus.Open.Analysis.CompletedThetaPositiveDefinite11936

/-- Claim 11935: the literal completed-theta autocorrelation has the
Fourier-square identity from the change of variables `u = y + d` and
`v = y - d`, together with the asserted real nonnegativity. -/
def claim11935 : Prop :=
  ∀ x : ℝ,
    completedThetaAutocorrelationFourier x =
        (1 / 2 : ℂ) * (completedThetaFourier x) ^ 2 ∧
      ((1 / 2 : ℂ) * (completedThetaFourier x) ^ 2).im = 0 ∧
        0 ≤ ((1 / 2 : ℂ) * (completedThetaFourier x) ^ 2).re

end

end MathlibPlus.Open.Analysis.CompletedThetaAutocorrelation
