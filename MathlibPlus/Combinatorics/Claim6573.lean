import Mathlib.Data.Set.Function
import Mathlib.Tactic.Abel

namespace MathlibPlus.Combinatorics.Claim6573

/-!
Statement-fidelity formalization of claim 6573.  The hypothesis `htransport`
records the source graph transport from `S` to `q(S)`; the conclusion is the
conjugated source translation `u ↦ q (q⁻¹ u + t)` and its preservation of the
Cayley difference relation on `q(S)`.
-/

/-- A transported source translation is an automorphism of the transported
Cayley relation. -/
theorem conjugated_translation_preserves_image_cayley
    {V : Type*} [AddCommGroup V]
    (S : Set V) (q : V ≃ V)
    (htransport : ∀ x y : V,
      q x - q y ∈ q '' S ↔ x - y ∈ S)
    (t : V) :
    Function.Bijective (fun u : V => q (q.symm u + t)) ∧
      ∀ u v : V,
        q (q.symm u + t) - q (q.symm v + t) ∈ q '' S ↔
          u - v ∈ q '' S := by
  constructor
  · constructor
    · intro u v huv
      have hsum : q.symm u + t = q.symm v + t := q.injective huv
      have hsymm : q.symm u = q.symm v := add_right_cancel hsum
      exact q.symm.injective hsymm
    · intro u
      refine ⟨q (q.symm u - t), ?_⟩
      simp [sub_add_cancel]
  · intro u v
    calc
      q (q.symm u + t) - q (q.symm v + t) ∈ q '' S ↔
          (q.symm u + t) - (q.symm v + t) ∈ S :=
        htransport _ _
      _ ↔ q.symm u - q.symm v ∈ S := by
        rw [show (q.symm u + t) - (q.symm v + t) =
            q.symm u - q.symm v by abel]
      _ ↔ u - v ∈ q '' S := by
        simpa using (htransport (q.symm u) (q.symm v)).symm

end MathlibPlus.Combinatorics.Claim6573
