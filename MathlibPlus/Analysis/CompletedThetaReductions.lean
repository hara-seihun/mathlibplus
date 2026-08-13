import MathlibPlus.Open.Analysis.CompletedTheta
import MathlibPlus.Open.Analysis.CompletedThetaSixMoments

namespace MathlibPlus.Analysis.CompletedTheta

open MathlibPlus.Open.Analysis.CompletedTheta

/-- The six certified moment bounds imply the four-bound prefix. -/
theorem certifiedFirstSixMoments_implies_certifiedFirstFourMoments :
    certifiedFirstSixMoments → certifiedFirstFourMoments := by
  intro h
  dsimp [certifiedFirstSixMoments] at h
  dsimp [certifiedFirstFourMoments]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end MathlibPlus.Analysis.CompletedTheta
