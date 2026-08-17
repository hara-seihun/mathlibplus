import MathlibPlus.Open.Analysis.EntireMellinSampleSum

namespace MathlibPlus.Open.ResearchFormalization.Claim3642

noncomputable section

open MathlibPlus.Open.Analysis

/-- Claim 3642: an exact-S0 source has a smooth, eventually vanishing,
zero-flat positive sample sum. -/
def smoothCompactZeroFlatSampleSum3642 : Prop :=
  ∀ q : ℝ → ℝ,
    exactS0Source q →
      smoothCompactFlatSampleSum q

end

end MathlibPlus.Open.ResearchFormalization.Claim3642
