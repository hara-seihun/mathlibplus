import MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.LiCayleyZeroModeTransform15370

noncomputable section

open MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

/-- Claim 15370: the exact Li--Cayley zero-mode transform. -/
def exactLiCayleyZeroModeTransform_claim15370 : Prop :=
  ∀ (d : ℕ) (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
    let zρ : ℂ := 1 - 1 / ρ
    (∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-((1 - ρ) * (t : ℂ))) * (laguerreTwo d t : ℂ)) =
      (d + 1 : ℂ) + ρ + (1 - ρ) * zρ ^ (-(d + 2 : ℤ))

end

end MathlibPlus.Open.ResearchFormalization.LiCayleyZeroModeTransform15370
