import MathlibPlus.Analysis.ClaimDefinitions20260811

namespace MathlibPlus.Open.NewResearch2.O0340

/-- Claim 15542: the completed archimedean density is negative on the ray
`t ≥ log 2`. -/
def claim15542 : Prop :=
  ∀ t : ℝ,
    Real.log 2 ≤ t →
      MathlibPlus.Analysis.Claim15541.completedArchimedeanDensity t < 0

end MathlibPlus.Open.NewResearch2.O0340
