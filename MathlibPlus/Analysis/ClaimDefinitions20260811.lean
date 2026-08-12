import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim18090

/-- The gamma-shift operator `ℒ f(t) = ((1 - 2t)/(4π)) f(t+2)`. -/
noncomputable def gammaShiftOperator (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((1 - 2 * t) / (4 * Real.pi)) * f (t + 2)

end MathlibPlus.Analysis.Claim18090

namespace MathlibPlus.Analysis.Claim15541

/-- The completed archimedean density `κ(t)`. -/
noncomputable def completedArchimedeanDensity (t : ℝ) : ℝ :=
  t * ((Real.exp (2 * t) - 1)⁻¹ - Real.exp t)

end MathlibPlus.Analysis.Claim15541
