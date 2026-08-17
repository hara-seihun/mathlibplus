import MathlibPlus.Analysis.CompletedGammaFactor

namespace MathlibPlus.Open.ResearchFormalization.O0328ArchimedeanGrowth15474

open Filter

noncomputable section

/-- The positive-real root scale of the canonical completed factor samples. -/
noncomputable def completedGammaSampleRoot (n : ℕ) : ℝ :=
  Real.rpow
    ‖MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor
      (2 * (n : ℂ) + 1)‖
    (1 / (2 * (n : ℝ)))

/-- Claim 15474: the completed-factor root scale is asymptotic to the stated
archimedean square-root scale. -/
def claim15474 : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    completedGammaSampleRoot
    (fun n : ℕ =>
      Real.sqrt ((n : ℝ) / (Real.exp 1 * Real.pi)))

end

end MathlibPlus.Open.ResearchFormalization.O0328ArchimedeanGrowth15474
