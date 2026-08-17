import MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879

namespace MathlibPlus.Open.ResearchFormalization.Q0134GoodBad

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879

/-- A vertex of the finite planar point set is good exactly when every
positive radius class among the other points has cardinality at most three. -/
def goodCenter (P : Finset Plane) (v : Plane) : Prop :=
  v ∈ P ∧
    ∀ r : ℝ, 0 < r → (radiusClass P v r).card ≤ 3

/-- A bad configuration is a strict-convex finite point set for which every
vertex has a positive radius class containing at least four other vertices. -/
def badConfiguration (P : Finset Plane) : Prop :=
  strictConvexPointSet P ∧
    ∀ v ∈ P, ∃ r : ℝ, 0 < r ∧ 4 ≤ (radiusClass P v r).card

end

end MathlibPlus.Open.ResearchFormalization.Q0134GoodBad
