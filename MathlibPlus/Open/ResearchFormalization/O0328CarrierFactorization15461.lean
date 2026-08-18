import MathlibPlus.Open.NewResearch2.O0328
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328CarrierFactorization15461

noncomputable section

/-- Claim 15461: the reviewed `fullMellinCarrier` is the common full
Poisson/Mellin carrier denoted by both `X_q^P` and `𝓗_q`; its centered
factorization and the corresponding arithmetic-coordinate factorization are
recorded with the reviewed Xi, multiplier, zeta, and arithmetic-carrier
objects. -/
def claim15461 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                a R →
            (∀ z : ℂ,
              MathlibPlus.Open.NewResearch2.O0328.fullMellinCarrier q z =
                MathlibPlus.Open.NewResearch2.O0328.xiCarrier z *
                  MathlibPlus.Open.NewResearch2.O0328.xiNormalizedMellinMultiplier q z) ∧
              (∀ s : ℂ,
                MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.arithmeticCarrier
                    q s =
                  riemannZeta s *
                    MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.arithmeticMultiplier
                      q s)

end

end MathlibPlus.Open.ResearchFormalization.O0328CarrierFactorization15461
