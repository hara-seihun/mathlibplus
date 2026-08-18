import MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

namespace MathlibPlus.Open.ResearchFormalization.Q0134.Claim16874

open MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
open MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

noncomputable section

/-- The two exact strict-convex threshold-three counterexample assertions. -/
def thresholdThreeCounterexamples_claim16874 : Prop :=
  (∃ P : Finset Plane,
      P.card = 9 ∧
        strictConvexPointSet P ∧
          ∀ v ∈ P,
            ∃ r : ℝ, 0 < r ∧ 3 ≤ (radiusClass P v r).card) ∧
    (∃ P : Finset Plane,
      P.card = 20 ∧
        strictConvexPointSet P ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ v ∈ P, 3 ≤ (radiusClass P v r).card)

end

end MathlibPlus.Open.ResearchFormalization.Q0134.Claim16874
