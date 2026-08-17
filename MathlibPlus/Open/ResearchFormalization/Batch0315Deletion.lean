import MathlibPlus.Open.ResearchFormalization.Batch0315

namespace MathlibPlus.Open.ResearchFormalization.Batch0315Deletion

open MathlibPlus.Open.ResearchFormalization.Batch0315
open scoped BigOperators

def exactThreeTraceBranch (F : Family) : Prop :=
  unionClosed F ∧
    projectsToT F ∧
    (∀ i : TightIndex, 2 * frequency F (t i) = F.card - 1) ∧
    (∀ A : Finset Coordinate, removable F A → (A ∩ T).card ≤ 1)

def deletionCount (D : Finset (Finset Coordinate)) (i : TightIndex) : ℕ :=
  (D.filter (fun A => t i ∈ A)).card

/-- Claim 19717: under the exact-three removable-member incidence condition,
three-coordinate deletion counting is automatic. -/
def simultaneousDeletionAutomatic : Prop :=
  ∀ (F : Family) (D : Finset (Finset Coordinate)),
    exactThreeTraceBranch F →
    D.Nonempty →
    (∀ A ∈ D, removable F A) →
    (∑ i : TightIndex, deletionCount D i) ≤ D.card ∧
      ∃ i : TightIndex,
        deletionCount D i ≤ D.card / 3 ∧
          D.card / 3 ≤ (D.card - 1) / 2 ∧
            1 + 2 * deletionCount D i ≤ D.card

end MathlibPlus.Open.ResearchFormalization.Batch0315Deletion
