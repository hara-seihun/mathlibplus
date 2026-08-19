import MathlibPlus.Open.ResearchFormalization.CompletedCenteredWeil10349

namespace MathlibPlus.Open.ResearchFormalization.O0028Claim10337

open MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

noncomputable section

/-- The completed xi normalization in the admitted source. -/
noncomputable def completedXi10337 (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.cpow (Real.pi : ℂ) (-s / 2) *
    Complex.Gamma (s / 2) * riemannZeta s

/-- Claim 10337: the completed xi formula and the exact Weil-test transform,
reflected product, and autocorrelation carriers. -/
def completedXiAndWeilTestTransform_claim10337 : Prop :=
  (∀ s : ℂ,
    completedXi10337 s =
      (1 / 2 : ℂ) * s * (s - 1) *
        Complex.cpow (Real.pi : ℂ) (-s / 2) *
        Complex.Gamma (s / 2) * riemannZeta s) ∧
    (∀ (φ : ℝ → ℝ),
      realEvenCompactTest φ →
        (∀ z : ℂ,
          testFourierTransform φ z =
            ∫ u : ℝ, (φ u : ℂ) *
              Complex.exp (Complex.I * z * (u : ℂ))) ∧
        (∀ z : ℂ,
          testH φ z =
            testFourierTransform φ z *
              star (testFourierTransform φ (star z))) ∧
        (∀ u : ℝ,
          testAutocorrelation φ u =
            ∫ v : ℝ, φ (v + u) * φ v))

end

end MathlibPlus.Open.ResearchFormalization.O0028Claim10337
