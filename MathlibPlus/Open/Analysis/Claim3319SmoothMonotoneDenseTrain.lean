import MathlibPlus.Open.Analysis.Claim3324

namespace MathlibPlus.Open.Analysis.Claim3319

/-- Claim 3319: the smooth monotone dense-train hypothesis is the reviewed
scale-indexed carrier used by the shifted Blaschke estimates. -/
def smoothMonotoneDenseTrain_claim3319
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ) (d eta q R : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (p r Y dLimit : ℝ) : Prop :=
  MathlibPlus.Open.Analysis.Claim3326.smoothMonotoneDenseTrain
    N y t d eta q R g p r Y dLimit

end MathlibPlus.Open.Analysis.Claim3319
