import MathlibPlus.Open.Research.NonsplitSingerLiftObstruction

namespace MathlibPlus.Open.Research.R2712

open MathlibPlus.Open.Research.NonsplitSingerLiftObstruction
open MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

/-- Claim 42367: in the quotient carrier `C₂ × V` for the odd ranks of the
    nonsplit Singer-cover datum, every linear map on `V`, extended by the
    identity on `C₂`, preserves the complete quotient color partition.  The
    imported `quotientColor` is the diagonal, the nonidentity `C₂` point, and
    the two nonzero-`V` layers, while `quotientMap` is the displayed action on
    the quotient carrier. -/
def claim42367 : Prop :=
  ∀ r : ℕ, (r = 3 ∨ r = 5 ∨ r = 7) →
    ∀ B : F3Vector r ≃ₗ[ZMod 3] F3Vector r,
      preservesQuotientColors B

end MathlibPlus.Open.Research.R2712
