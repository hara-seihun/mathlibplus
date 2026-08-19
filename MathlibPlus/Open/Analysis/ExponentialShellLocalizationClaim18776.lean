import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Open.Analysis.ExponentialShellLocalizationClaim18776

open MathlibPlus.Analysis.ThetaMellin

noncomputable section

private noncomputable def shellScale (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2

private noncomputable def shellDeformation (c : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑' n : ℕ, c n * thetaShell n u

/-- The exact exponentially localized coefficient class for the canonical
completed-theta shell deformation. -/
def exponentiallyLocalizedShellCoefficientClass_claim18776
    (c : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    Summable (fun n : ℕ =>
      |c n| * shellScale n * Real.exp (δ * shellScale n))

end

end MathlibPlus.Open.Analysis.ExponentialShellLocalizationClaim18776
