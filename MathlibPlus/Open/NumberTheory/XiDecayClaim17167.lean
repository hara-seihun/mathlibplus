import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.Open.NumberTheory.XiDecayClaim17167

open MathlibPlus.NumberTheory.CompletedZetaRadial

/-- Claim 17167: the canonical completed xi function tends to zero on the
critical line as the real parameter tends to infinity in absolute value. -/
def xiDecayOnCriticalLine_claim17167 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T < |t| →
        ‖riemannXi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ < ε

end MathlibPlus.Open.NumberTheory.XiDecayClaim17167
