import MathlibPlus.Open.ResearchFormalization.Batch0315

namespace MathlibPlus.Open.ResearchFormalization.Batch0315Deduplication

open MathlibPlus.Open.ResearchFormalization.Batch0315

 def deduplicatedSupport : Family := W.toFinset

/-- Claim 19722: deduplication leaves the ordinary full cube and removes the
weighted negative margins. -/
def deduplicationDestroysNegativeMargins : Prop :=
  deduplicatedSupport = X.powerset ∧
    W.card ≠ deduplicatedSupport.card ∧
    (∀ x : Coordinate, coefficient deduplicatedSupport x = 0) ∧
    unionClosed deduplicatedSupport

end MathlibPlus.Open.ResearchFormalization.Batch0315Deduplication
