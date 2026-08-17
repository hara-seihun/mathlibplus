import MathlibPlus.Open.Analysis.CompletedThetaToeplitz

namespace MathlibPlus.Open.Analysis.CompletedThetaConditionalVariance11937

noncomputable section

/-- Claim 11937: the normalized even two-copy density has zero conditional
mean and variance equal to the completed-theta quotient. -/
def claim11937 : Prop :=
  let density : ℝ → ℝ → ℝ := fun y d =>
    completedThetaSource (y + d) * completedThetaSource (y - d) /
      completedThetaAutocorrelation y
  (∀ y d : ℝ, 0 ≤ density y d) ∧
    (∀ y : ℝ, 0 < completedThetaAutocorrelation y) ∧
      (∀ y d : ℝ, density y d = density y (-d)) ∧
        (∀ y : ℝ, ∫ d : ℝ, d * density y d = 0) ∧
          (∀ y : ℝ,
            ∫ d : ℝ, d ^ 2 * density y d = completedThetaQuotient y) ∧
            (∀ y : ℝ,
              completedThetaQuotient y =
                completedThetaSecondMoment y /
                  completedThetaAutocorrelation y)

end

end MathlibPlus.Open.Analysis.CompletedThetaConditionalVariance11937
