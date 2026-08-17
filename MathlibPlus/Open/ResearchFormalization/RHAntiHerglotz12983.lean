import MathlibPlus.Open.ResearchFormalization.Claims12988_12990

namespace MathlibPlus.Open.ResearchFormalization.RHAntiHerglotz12983

open MathlibPlus.Open.ResearchFormalization

/-- Under RH, every positive finite frequency has the Cayley form and the
strict anti-Herglotz sign on the whole upper half-plane. -/
def claim12983 : Prop :=
  RiemannHypothesis →
    ∀ t : ℝ, 0 < t →
      let S_t : ℂ → ℂ := fun z =>
        centeredE (qMinus t z) / centeredE (qPlus t z)
      DifferentiableOn ℂ (centeredF t) {z : ℂ | 0 < z.im} ∧
        ∀ z : ℂ, 0 < z.im →
          centeredE (qPlus t z) ≠ 0 ∧
            ‖S_t z‖ < 1 ∧
            1 + S_t z ≠ 0 ∧
            centeredF t z =
              -(Complex.I / (t : ℂ)) *
                ((1 : ℂ) - S_t z) / ((1 : ℂ) + S_t z) ∧
            (centeredF t z).im < 0

end MathlibPlus.Open.ResearchFormalization.RHAntiHerglotz12983
