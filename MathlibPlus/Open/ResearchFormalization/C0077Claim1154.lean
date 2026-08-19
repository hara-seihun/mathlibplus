import MathlibPlus.Open.FormalizationBatch.AdmittedClaims1158And1166
import MathlibPlus.Open.ResearchFormalization.Claim1159

namespace MathlibPlus.Open.ResearchFormalization.Claim1154

open MathlibPlus.Open.FormalizationBatch
open MathlibPlus.Open.ResearchFormalization.Claim1159

/-- Newton's divided-difference representation of every positive-index flagged row. -/
def newtonDividedDifferenceRepresentation_claim1154 : Prop :=
  ∀ (a : ℝ) (m j : ℕ), 0 < m →
    flaggedArrayEntry a (m - 1) j =
      (m : ℝ) * dividedDifference a m (fun x => x ^ (2 * j))

end MathlibPlus.Open.ResearchFormalization.Claim1154
