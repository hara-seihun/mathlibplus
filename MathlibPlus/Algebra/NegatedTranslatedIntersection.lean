import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card

namespace MathlibPlus.Algebra.NegatedTranslatedIntersection

/-- Negation bijects the two intersections in claim 48130. -/
theorem card_negated_translated_intersection (T : ℤ) (U : Finset ℤ) :
    (U.image (fun u => -u) ∩ U.image (fun u => T + u)).card =
      (U ∩ U.image (fun u => -T - u)).card := by
  classical
  let A : Finset ℤ := U.image (fun u => -u) ∩ U.image (fun u => T + u)
  let B : Finset ℤ := U ∩ U.image (fun u => -T - u)
  let e : {z // z ∈ A} ≃ {z // z ∈ B} :=
    { toFun := fun z =>
        ⟨-z.1, by
          have hz :
              (∃ u ∈ U, -u = z.1) ∧ (∃ v ∈ U, T + v = z.1) := by
            simpa only [A, Finset.mem_inter, Finset.mem_image] using z.2
          simp only [B, Finset.mem_inter, Finset.mem_image]
          rcases hz with ⟨⟨u, hu, hzu⟩, ⟨v, hv, hzv⟩⟩
          constructor
          · rw [← hzu]
            simpa using hu
          · exact ⟨v, hv, by rw [← hzv]; simp [Int.sub_eq_add_neg, Int.neg_add]⟩⟩
      invFun := fun z =>
        ⟨-z.1, by
          have hz : z.1 ∈ U ∧ (∃ v ∈ U, -T - v = z.1) := by
            simpa only [B, Finset.mem_inter, Finset.mem_image] using z.2
          simp only [A, Finset.mem_inter, Finset.mem_image]
          rcases hz with ⟨hzU, ⟨v, hv, hzv⟩⟩
          constructor
          · exact ⟨z.1, hzU, by simp⟩
          · exact ⟨v, hv, by rw [← hzv]; simp [Int.sub_eq_add_neg, Int.neg_add]⟩⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro z; apply Subtype.ext; simp }
  simpa [A, B] using Fintype.card_congr e

end MathlibPlus.Algebra.NegatedTranslatedIntersection
