import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

namespace MathlibPlus.Combinatorics

/--
If `S` records the saturated members of three sources, while `K` contains a
common top and a distinct coatom for every source outside `S`, then the top
and those coatoms give the lower bound `4 - S.card`.
-/
theorem claim22171_product_card_ge_four_sub_saturated
    {α : Type*} [DecidableEq α]
    (K : Finset α) (top : α) (coatom : Fin 3 → α) (S : Finset (Fin 3))
    (htop : top ∈ K)
    (hcoatom : ∀ i, i ∉ S → coatom i ∈ K)
    (hcoatom_inj : Function.Injective coatom)
    (htop_ne_coatom : ∀ i, coatom i ≠ top) :
    4 - S.card ≤ K.card := by
  let U : Finset (Fin 3) := Finset.univ \ S
  have hUcard : U.card = 3 - S.card := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
  have himage : (U.image coatom).card = U.card :=
    Finset.card_image_iff.mpr hcoatom_inj.injOn
  have htop_image : top ∉ U.image coatom := by
    intro h
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp h
    exact htop_ne_coatom i hEq
  let A : Finset α := insert top (U.image coatom)
  have hA_sub : A ⊆ K := by
    intro x hx
    dsimp [A] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact htop
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hcoatom i (Finset.mem_sdiff.mp hi).2
  have hAcard : A.card = 1 + U.card := by
    dsimp [A]
    rw [Finset.card_insert_of_notMem htop_image, himage]
    omega
  have hle : A.card ≤ K.card := Finset.card_le_card hA_sub
  rw [hAcard, hUcard] at hle
  omega

end MathlibPlus.Combinatorics
