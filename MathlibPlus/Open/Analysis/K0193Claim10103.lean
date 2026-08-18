import MathlibPlus.Open.Analysis.CriticalPoissonSmoothing

namespace MathlibPlus.Open.Analysis.K0193Claim10103

noncomputable section

/-- The finite-place Li moment is the natural-cutoff limit of the centered
Laguerre integral for every positive index. -/
def claim10103 : Prop :=
  ∀ n : ℕ, 0 < n →
    Filter.Tendsto (criticalCenteredFinitePlaceMoment n) Filter.atTop
      (nhds (criticalSf n))

end

end MathlibPlus.Open.Analysis.K0193Claim10103
