import Mathlib

namespace MathlibPlus.GroupTheory.ComplementaryValency

/--
Formalization of admitted claim 29734.  The product of residue-class groups is
used as an additive model of `C₂³ × C₃²`; an inverse-closed connection set of
valency eleven occupies eleven of the seventy-one nonzero elements, leaving
sixty elements in its complement.
-/
theorem complementaryValency
    (S : Finset ((ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)))
    (hS : S ⊆
      (Finset.univ.erase
        (0 : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3))))
    (hcard : S.card = 11)
    (_hinv : ∀ g, g ∈ S → -g ∈ S) :
    Fintype.card ((ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)) = 72 ∧
      ((Finset.univ.erase
        (0 : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3))) \ S).card = 60 := by
  have hcardG :
      Fintype.card ((ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)) = 72 := by
    simp [ZMod.card]
  refine ⟨hcardG, ?_⟩
  have hbase :
      (Finset.univ.erase
        (0 : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3))).card = 71 := by
    simp [ZMod.card]
  rw [Finset.card_sdiff_of_subset hS, hbase, hcard]

end MathlibPlus.GroupTheory.ComplementaryValency
