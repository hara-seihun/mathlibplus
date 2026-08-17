import MathlibPlus.Open.Analysis.CompletedThetaToeplitz

namespace MathlibPlus.Open.Analysis.CompletedThetaAutocorrelation11934

noncomputable section

/-- Claim 11934: the two-copy completed-theta autocorrelation, second moment,
and quotient carriers. -/
def claim11934 : Prop :=
  ∀ y : ℝ,
    completedThetaAutocorrelation y =
        ∫ d : ℝ,
          completedThetaSource (y + d) * completedThetaSource (y - d) ∧
      completedThetaSecondMoment y =
        ∫ d : ℝ,
          d ^ 2 * completedThetaSource (y + d) * completedThetaSource (y - d) ∧
      completedThetaQuotient y =
        completedThetaSecondMoment y / completedThetaAutocorrelation y

end

end MathlibPlus.Open.Analysis.CompletedThetaAutocorrelation11934
