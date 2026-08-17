import MathlibPlus.Open.ResearchFormalization.R0264Claim19305

namespace MathlibPlus.Open.ResearchFormalization.R0264Claim19304

noncomputable section

open MathlibPlus.Open.NewResearch2.R0264Repair
open MathlibPlus.Open.ResearchFormalization.R0264Claim19305

/-- Claim 19304: the exact modular boundary-port coefficients are the
    displayed A_lambda and B_lambda values. -/
def claim19304_modularIntegrationByPartsBoundaryPort : Prop :=
  ∀ (α lam u z c : ℝ),
    boundaryPort α lam u z c =
      (-(α / 4) *
          (1 + u / 2 - 2 * lam * u * Real.exp (2 * u)) +
        z * ((1 + u / 2 - 2 * lam * u * Real.exp (2 * u)) / 4 - 1 / 2)) * c

end

end MathlibPlus.Open.ResearchFormalization.R0264Claim19304
