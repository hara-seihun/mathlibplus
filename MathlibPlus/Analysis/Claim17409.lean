import Mathlib

namespace MathlibPlus.Analysis.Claim17409

/-- Jump energy of a real-valued function at a real shift. -/
noncomputable def jumpEnergy (f : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ x : ℝ, |f (x + ℓ) - f x| ^ 2

theorem jumpEnergy_eq_integral (f : ℝ → ℝ) (ℓ : ℝ) :
    jumpEnergy f ℓ = ∫ x : ℝ, |f (x + ℓ) - f x| ^ 2 := by
  rfl

end MathlibPlus.Analysis.Claim17409
