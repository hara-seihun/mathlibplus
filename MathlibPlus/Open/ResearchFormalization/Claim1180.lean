import MathlibPlus.Open.C0079FlaggedArrayClaim1178
import MathlibPlus.Open.C0079PartitionMinorsClaim1179
import MathlibPlus.Open.C0079AreaThreeCoordinates

namespace MathlibPlus.Open.ResearchFormalization.Claim1180

open MathlibPlus.Open.C0079

noncomputable section

/-- Claim 1180: with the exact half-shifted variables and the fixed principal
flagged-minor carrier, the principal determinant is the pair-sum product. -/
def halfShiftAndPrincipalProduct_claim1180 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (a b : ℝ), b = a - 1 / 2 →
    let X : ℝ := 2 * b + (d : ℝ) + 1
    let Y : ℝ := 2 * a + (d : ℝ)
    let P_d : ℝ := principalProduct1181 d b
    X = Y ∧
      emptyMinor d a = P_d

end

end MathlibPlus.Open.ResearchFormalization.Claim1180
