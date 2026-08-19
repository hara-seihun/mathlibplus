import Mathlib
import MathlibPlus.Open.Research.FormalizationR0375

namespace MathlibPlus.Open.ResearchFormalization.R0375Claim20570

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

open MathlibPlus.Open.Research.R0375

private def graphIsoClass {n : ℕ} (F : SimpleGraph (Fin n)) :
    Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) | Nonempty (G ≃g F)}

private def rankSubgraphs {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).filter
    (fun F => F ≤ G ∧ Set.ncard F.edgeSet = j)

private def lowerShadow {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) :
    Multiset (Set (SimpleGraph (Fin n))) :=
  (rankSubgraphs G j).val.map graphIsoClass

private def firstShadowSituation {n : ℕ}
    (G H : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ¬ Nonempty (G ≃g H) ∧
    Set.ncard G.edgeSet = Set.ncard H.edgeSet ∧
    (∀ j : ℕ, j < r → lowerShadow G j = lowerShadow H j) ∧
    lowerShadow G r ≠ lowerShadow H r ∧
    n - 1 ≤ r

/-- Claim 20570: under the exact first-nonzero lower-shadow setup, every
spanning tree has the source edge count, exponential incidence floor, and
reviewed orbit-stabilizer incidence identity. -/
def spanningTreeHostSpecificFloor_claim20570 : Prop :=
  ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (r : ℕ),
    firstShadowSituation G H r →
      ∀ T : SimpleGraph (Fin n),
        T ≤ G →
        T.IsTree →
          edgeCount T = n - 1 ∧
            (2 : ℚ) ^ ((r : ℤ) - (n : ℤ)) ≤
              (spanningSubgraphCount n T G : ℚ) *
                  (automorphismCard n T : ℚ) /
                automorphismCard n G ∧
            (spanningSubgraphCount n T G : ℚ) *
                  (automorphismCard n T : ℚ) /
                automorphismCard n G =
              (hostOrbitIncidence n G T : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0375Claim20570
