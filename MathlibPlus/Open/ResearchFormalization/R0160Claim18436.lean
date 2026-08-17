import MathlibPlus.Open.Analysis.WeightedShellWatsonClaims18438_18442

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0160Claim18436

noncomputable section

open MathlibPlus.Open.Analysis

/-- The exact Gamma-density expectation identity for the weighted shell
moment, with the shell, rate, shape, remainder, and normalization retained. -/
def claim18436 : Prop :=
  ∀ (m j : ℕ),
    1 ≤ m →
      weightedShellMoment_claim18438 m j =
        (2 * Real.exp (-weightedShellA_claim18438 m) /
            weightedShellRho_claim18438 m ^ weightedShellNu_claim18438 j) *
          weightedShellExponentialExpectation_claim18436 m j

end

end MathlibPlus.Open.ResearchFormalization.R0160Claim18436
