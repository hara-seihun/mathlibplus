import Mathlib
import MathlibPlus.Open.Research.FormalizationR0375

namespace MathlibPlus.Open.ResearchFormalization.R0375Claim20571

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

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

private def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup
    (fun v => Nat.card {w : Fin n // G.Adj v w})

/-- Claim 20571: under the exact first-nonzero lower-shadow setup, a connected
host with maximum degree Delta satisfies the displayed degree-only floor. -/
def boundedDegreeHostFloor_claim20571 : Prop :=
  ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (r Δ : ℕ),
    firstShadowSituation G H r →
      G.Connected →
      maximumDegree G = Δ →
        (2 : ℚ) ^ ((r : ℤ) - (n : ℤ)) ≤
          (n : ℚ) * (Nat.factorial Δ : ℚ) *
            ((Δ - 1 : ℕ) ^ (n - Δ - 1) : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0375Claim20571
