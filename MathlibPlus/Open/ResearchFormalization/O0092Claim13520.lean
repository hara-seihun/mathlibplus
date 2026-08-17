import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0092Claim13536

namespace MathlibPlus.Open.ResearchFormalization.O0092

noncomputable section

/-- The least separated width in the split/compact tensor-product span. -/
noncomputable def splitCompactSeparationRank
    (R : ℝ → ℝ → ℂ)
    (hR : ∃ r : ℕ, hasSeparatedRepresentation R r) : ℕ :=
  letI := Classical.decPred (hasSeparatedRepresentation R)
  Nat.find hR

/-- Separation rank is the least width of a separated representation with a
split factor in `span{1, cosh, sinh}` and a compact factor in
`span{1, cos, sin}`. -/
def claim13520 : Prop :=
  ∀ (R : ℝ → ℝ → ℂ)
    (hR : ∃ r : ℕ, hasSeparatedRepresentation R r),
    separationRankExactly R (splitCompactSeparationRank R hR)

end

end MathlibPlus.Open.ResearchFormalization.O0092
