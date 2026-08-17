import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A finite planar point set is in strict convex position when every point is
outside the convex hull of the remaining points. -/
def strictConvexPointSet (P : Finset Plane) : Prop :=
  P.Nonempty ∧
    ∀ v ∈ P, v ∉ convexHull ℝ (↑(P.erase v) : Set Plane)

/-- The positive-radius class of points on the circle centered at v. -/
noncomputable def radiusClass
    (P : Finset Plane) (v : Plane) (r : ℝ) : Finset Plane :=
  (P.erase v).filter (fun w => dist v w = r)

/-- A bad configuration is strict-convex and every vertex has a positive
radius class containing at least four other vertices. -/
def badConfiguration (P : Finset Plane) : Prop :=
  strictConvexPointSet P ∧
    ∀ v ∈ P, ∃ r : ℝ, 0 < r ∧ 4 ≤ (radiusClass P v r).card

/-- A selected four-point witness class, retaining the selected four points
rather than replacing them by an unconstrained incidence family. -/
def selectedFourPointWitness
    (P : Finset Plane) (v : Plane) (r : ℝ) (Q : Finset Plane) : Prop :=
  Q.card = 4 ∧ Q ⊆ radiusClass P v r

/-- A globally shortest pairwise distance, with both attainment and the
lower-bound condition made explicit. -/
def globalShortestDistance (P : Finset Plane) (s : ℝ) : Prop :=
  (∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = s) ∧
    (∀ a ∈ P, ∀ b ∈ P, a ≠ b → s ≤ dist a b)

/-- Claim 16879: every radius supporting a selected four-point class in a bad
configuration is strictly larger than the globally shortest pairwise distance. -/
def claim16879 : Prop :=
  ∀ P : Finset Plane, badConfiguration P →
    ∀ v ∈ P, ∀ r : ℝ, ∀ Q : Finset Plane,
      0 < r →
        selectedFourPointWitness P v r Q →
          ∀ s : ℝ, globalShortestDistance P s → s < r

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
