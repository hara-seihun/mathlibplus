import Mathlib

namespace MathlibPlus.Order

/-- Claim 26651: every element of a finite join-semilattice with bottom is a
finite supremum of sup-irreducible (join-irreducible) elements. -/
theorem finiteJoinSemilattice_generated_by_joinIrreducibles
    (α : Type*) [SemilatticeSup α] [OrderBot α] [Fintype α] (a : α) :
    ∃ s : Finset α, s.sup id = a ∧ ∀ ⦃b : α⦄, b ∈ s → SupIrred b := by
  exact exists_supIrred_decomposition a

end MathlibPlus.Order
