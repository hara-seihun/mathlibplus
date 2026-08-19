import MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599

namespace MathlibPlus.Open.ResearchFormalization.R0849Claim29597

noncomputable section

/-- Claim 29597: at an all-distinct first positive packing split, the
source cross-ratio identity is the identical cross-ratio identity for the
four connected-packing forms at that split. -/
def claim29597 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V),
    (∀ i : Fin 4, (F i).IsAcyclic) →
    _root_.MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.pairwiseDistinctForestUPolynomials F →
    ∀ lam : ℚ,
      lam ≠ 0 → lam ≠ 1 →
      _root_.MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.sourceCrossRatio F lam →
    ∀ h : ℕ,
      _root_.MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.firstPositivePackingSplit F h →
      _root_.MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.rowsAllDistinctAt F h →
      _root_.MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599.packingCrossRatio F lam h

end

end MathlibPlus.Open.ResearchFormalization.R0849Claim29597
