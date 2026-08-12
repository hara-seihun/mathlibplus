import Mathlib

namespace MathlibPlus.Combinatorics.LargestProperPacking

/-- Claim 27378: a proper set of codimension one in a finite vertex set
leaves room for no disjoint nonsingleton partner.  Connectedness is not used
in this set-theoretic obstruction. -/
theorem no_nonsingleton_partner
    {α : Type*} [DecidableEq α]
    (M : ℕ) (V A : Finset α)
    (hV : V.card = M)
    (hA_sub : A ⊆ V)
    (hA_card : A.card = M - 1) :
    ¬ ∃ B : Finset α,
      B ⊆ V ∧ Disjoint A B ∧ 2 ≤ B.card := by
  rintro ⟨B, hB_sub, hdisjoint, hB_card⟩
  have hUnion_sub : A ∪ B ⊆ V := Finset.union_subset hA_sub hB_sub
  have hCard : (A ∪ B).card ≤ V.card :=
    Finset.card_le_card hUnion_sub
  rw [Finset.card_union_of_disjoint hdisjoint] at hCard
  omega

end MathlibPlus.Combinatorics.LargestProperPacking
