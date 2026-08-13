import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.NumberTheory.Claim17166

open MathlibPlus.NumberTheory.CompletedZetaRadial

/-- Affine translation of the critical-line boundary identity from claim 17166.
The source-specific entire function `H_{1/2}` is retained as a carrier, while the
completed xi function is the canonical `riemannXi` definition. -/
theorem criticalLineEvaluation_claim17166
    (Hhalf : ℂ → ℂ)
    (hboundary : ∀ t : ℝ,
      Hhalf (-(t : ℂ)^2) =
        riemannXi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) :
    ∀ (c t : ℝ),
      let Hc : ℂ → ℂ := fun w => Hhalf w + ((c : ℂ) - (1 / 2 : ℂ))
      Hc (-(t : ℂ)^2) =
        riemannXi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
          ((c : ℂ) - (1 / 2 : ℂ)) := by
  intro c t
  dsimp
  rw [hboundary t]

end MathlibPlus.NumberTheory.Claim17166
