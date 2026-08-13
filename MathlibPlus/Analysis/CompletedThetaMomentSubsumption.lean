import MathlibPlus.Open.Analysis.CompletedTheta
import MathlibPlus.Open.Analysis.CompletedThetaSixMoments

namespace MathlibPlus.Analysis.CompletedTheta

open MathlibPlus.Open.Analysis.CompletedTheta

/-- Six certified completed-theta moment bounds include the four-moment bounds. -/
theorem certifiedFirstSixMoments_implies_certifiedFirstFourMoments :
    certifiedFirstSixMoments → certifiedFirstFourMoments := by
  intro h
  dsimp only [certifiedFirstSixMoments] at h
  dsimp only [certifiedFirstFourMoments]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end MathlibPlus.Analysis.CompletedTheta
