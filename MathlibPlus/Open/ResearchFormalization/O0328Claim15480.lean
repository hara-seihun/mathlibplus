import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
import MathlibPlus.Open.ResearchFormalization.O0328Claim15463
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328Claim15480

noncomputable section

/-- The even real-entire Laguerre--Pólya carrier used in the obstruction:
order at most one, even, real on the real axis, and with only real zeros. -/
def evenLaguerrePolyaFunction (G : ℂ → ℂ) : Prop :=
  MathlibPlus.Open.ResearchFormalization.O0328Claim15463.realEntireEvenOrderAtMostOne G ∧
    G ≠ 0 ∧
      ∀ z : ℂ, G z = 0 → z.im = 0

/-- Claim 15480: a nonzero center-flat compact-source multiplier has
infinitely many off-axis zeros and therefore admits no nonzero finite
polynomial times an even Laguerre--Pólya factorization. -/
def claim15480_multiplierNotPolynomialTimesEvenLaguerrePolya : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                a R →
            q ≠ 0 →
              Set.Infinite
                  {z : ℂ |
                    MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier
                          q z = 0 ∧
                      z.im ≠ 0} ∧
                ¬ ∃ (P : Polynomial ℂ) (G : ℂ → ℂ),
                    P ≠ 0 ∧
                      evenLaguerrePolyaFunction G ∧
                        ∀ z : ℂ,
                          MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier
                              q z =
                            P.eval z * G z

end

end MathlibPlus.Open.ResearchFormalization.O0328Claim15480
