import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim17072

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.FormalizationBatch

/-- Claim 17067: the exact table-prescribed order-eight witness has the
alternating-square pair and the five fixed component projections listed in the
source. -/
def claim17067_exactComponentProjections : Prop :=
  ∃ π : PointedLocalPermutations V8,
    involutiveFixedIndexCocycle π ∧
      tableFamily π ∧
        exactAlternatingSquareRegime π

end MathlibPlus.Open.ResearchFormalization
