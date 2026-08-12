import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-!
Formalization of admitted claim 26655.  `F` is the finite union-closed family
and `S` is the finite set of distinct selected nonempty union-irreducible
members.  The conclusion records both simultaneous removability (the
remaining family is union-closed) and the absence of a new representation of a
selected member by remaining members.
-/

/-- Distinct union-irreducible members can be removed simultaneously. -/
theorem simultaneousRemovalOfUnionIrreducibles
    {α : Type*} [DecidableEq α]
    (F S : Finset (Finset α))
    (h_union_closed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hS_irreducible : ∀ A ∈ S, A ∈ F ∧ A.Nonempty ∧
      ∀ B ∈ F, ∀ C ∈ F, B ∪ C = A → B = A ∨ C = A) :
    (∀ B ∈ F \ S, ∀ C ∈ F \ S, B ∪ C ∈ F \ S) ∧
    (∀ A ∈ S, ∀ B ∈ F \ S, ∀ C ∈ F \ S, B ∪ C ≠ A) := by
  constructor
  · intro B hB C hC
    have hBf : B ∈ F := (Finset.mem_sdiff.mp hB).1
    have hBs : B ∉ S := (Finset.mem_sdiff.mp hB).2
    have hCf : C ∈ F := (Finset.mem_sdiff.mp hC).1
    have hCs : C ∉ S := (Finset.mem_sdiff.mp hC).2
    have hBCF : B ∪ C ∈ F := h_union_closed B hBf C hCf
    by_contra hnot
    have hBCS : B ∪ C ∈ S := by
      by_contra h
      exact hnot (Finset.mem_sdiff.mpr ⟨hBCF, h⟩)
    have hcases := (hS_irreducible (B ∪ C) hBCS).2.2 B hBf C hCf rfl
    rcases hcases with hBA | hCA
    · exact hBs (hBA.symm ▸ hBCS)
    · exact hCs (hCA.symm ▸ hBCS)
  · intro A hA B hB C hC hEq
    have hBf : B ∈ F := (Finset.mem_sdiff.mp hB).1
    have hBs : B ∉ S := (Finset.mem_sdiff.mp hB).2
    have hCf : C ∈ F := (Finset.mem_sdiff.mp hC).1
    have hCs : C ∉ S := (Finset.mem_sdiff.mp hC).2
    have hcases := (hS_irreducible A hA).2.2 B hBf C hCf hEq
    rcases hcases with hBA | hCA
    · exact hBs (hBA.symm ▸ hA)
    · exact hCs (hCA.symm ▸ hA)

end MathlibPlus.Combinatorics
