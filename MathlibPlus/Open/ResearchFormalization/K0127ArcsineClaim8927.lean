import MathlibPlus.Open.Analysis.ExplicitLogarithmicPotentialDifference

namespace MathlibPlus.Open.ResearchFormalization.K0127ArcsineClaim8927

open MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 8927: the named equilibrium density has its arcsine-mixture representation. -/
def claim8927_arcsineMixtureRepresentation : Prop :=
  ∀ z : ℝ,
    equilibriumDensity potentialEndpoint z =
      2 * ∫ u in (0 : ℝ)..1,
        if 0 < z ∧ z < potentialEndpoint / u then
          1 / (Real.pi * Real.sqrt ((potentialEndpoint / u) ^ 2 - z ^ 2))
        else
          0

end

end MathlibPlus.Open.ResearchFormalization.K0127ArcsineClaim8927
