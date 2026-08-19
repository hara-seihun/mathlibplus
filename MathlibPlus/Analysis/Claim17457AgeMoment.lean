import Mathlib

namespace MathlibPlus.Analysis.Claim17457

noncomputable section

/-- The age moment `h_n` as the integral of the supplied weight against the
age-indexed kernel on the positive half-line. -/
noncomputable def ageMoment_claim17457
    (n : ℕ) (φ₁ : ℝ → ℝ) (B : ℕ → ℝ → ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), φ₁ v * B n v

end
end MathlibPlus.Analysis.Claim17457
