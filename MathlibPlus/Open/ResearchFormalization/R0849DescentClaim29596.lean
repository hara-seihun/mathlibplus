import MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599

open scoped BigOperators

open MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599

namespace MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29596

noncomputable section

/-- Claim 29596: for four acyclic forests on one common finite vertex carrier,
distinct ordinary U-polynomials have the common zeroth `K` row and a least
positive packing degree at which the four rows are not all equal. -/
def claim29596_firstPositivePackingSplit : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V),
    (∀ i : Fin 4, (F i).IsAcyclic) →
      pairwiseDistinctForestUPolynomials F →
        (∀ i : Fin 4,
          packingRow F 0 i =
            (MvPolynomial.X 0) ^ Fintype.card V) ∧
          ∃ h : ℕ, firstPositivePackingSplit F h

end

end MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29596
