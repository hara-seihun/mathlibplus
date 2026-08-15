import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_9953

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a005f519cc754a

/-- Central Euler diagonalization for the admitted annular zero-mean source class. -/
def centralEulerMellinDiagonalization : Prop :=
  ∀ (a R : ℝ),
    0 < a →
    a < R →
    ∀ (f : MathlibPlus.Open.ResearchFormalizationBatch_9953.Source a R) (s : ℂ),
      MathlibPlus.Open.ResearchFormalizationBatch_9953.mellinTransform
          (MathlibPlus.Open.ResearchFormalizationBatch_9953.centralEulerOperator a R f) s =
        -((s - (1 / 2 : ℂ)) ^ 2) *
          MathlibPlus.Open.ResearchFormalizationBatch_9953.mellinTransform f s

end MathlibPlus.Open.ResearchFormalizationBatch_01a005f519cc754a
