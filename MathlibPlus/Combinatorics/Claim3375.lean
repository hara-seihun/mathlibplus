import Mathlib

namespace MathlibPlus.Combinatorics.Claim3375

/-- Claim 3375: a union-closed family containing the empty set and a member
with singleton trace on each coordinate of `T` has the full powerset as its
projection to `T`. -/
theorem singletonTraces_force_full_boolean_cube
    {X : Type*} [DecidableEq X]
    (F : Set (Finset X)) (T : Finset X)
    (hUnion : ∀ {A B : Finset X}, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (hEmpty : ∅ ∈ F)
    (hSingleton : ∀ x ∈ T, ∃ A ∈ F, A ∩ T = {x}) :
    ∀ S : Finset X, S ⊆ T ↔ ∃ A ∈ F, A ∩ T = S := by
  have hrealize : ∀ S : Finset X, S ⊆ T → ∃ A ∈ F, A ∩ T = S := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨∅, hEmpty, by simp⟩
    | @insert x S hx ih =>
        intro hST
        have hxT : x ∈ T := hST (by simp)
        have hST' : S ⊆ T := by
          intro y hy
          exact hST (by simp [hy])
        obtain ⟨A, hAF, hA⟩ := hSingleton x hxT
        obtain ⟨B, hBF, hB⟩ := ih hST'
        refine ⟨A ∪ B, hUnion hAF hBF, ?_⟩
        calc
          (A ∪ B) ∩ T = (A ∩ T) ∪ (B ∩ T) := by
            ext y
            simp only [Finset.mem_inter, Finset.mem_union]
            tauto
          _ = {x} ∪ S := by rw [hA, hB]
          _ = insert x S := by rfl
  intro S
  constructor
  · exact hrealize S
  · rintro ⟨A, _hAF, hA⟩
    rw [← hA]
    exact Finset.inter_subset_right

end MathlibPlus.Combinatorics.Claim3375
