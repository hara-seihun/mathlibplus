import Mathlib

namespace MathlibPlus.Combinatorics.CanonicalCollision

/-- The canonical member omitting a coordinate is a lower member of a collision.

The hypothesis `hCollision` is the finite-set form of noninjectivity of the
projection which forgets `x`: it supplies a pair `A, A ∪ {x}` in the family.
The canonical member is the union of every family member omitting `x`. -/
theorem canonicalOmittedMember_lowerCollision
    {X : Type*} [DecidableEq X]
    (F : Finset (Finset X))
    (hUnion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (x : X)
    (hCollision : ∃ A, A ∈ F ∧ A ∪ {x} ∈ F ∧ x ∉ A) :
    let C := (F.filter (fun A => x ∉ A)).biUnion id
    C ∈ F ∧ C ∪ {x} ∈ F ∧ x ∉ C := by
  classical
  rcases hCollision with ⟨A, hA, hAx, hxA⟩
  let S : Finset (Finset X) := F.filter (fun B => x ∉ B)
  let C : Finset X := S.biUnion id
  have hA_S : A ∈ S := by
    simp [S, hA, hxA]
  have hS_mem : ∀ B ∈ S, B ∈ F := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hbiUnion_mem : ∀ T : Finset (Finset X),
      (∀ B ∈ T, B ∈ F) → T.Nonempty → T.biUnion id ∈ F := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _ hne
        exact False.elim (by simpa using hne)
    | @insert B T hB ih =>
        intro hT hne
        by_cases hTne : T.Nonempty
        · have hTail : T.biUnion id ∈ F :=
            ih (fun D hD => hT D (Finset.mem_insert_of_mem hD)) hTne
          have hBoth := hUnion B (hT B (Finset.mem_insert_self B T))
            (T.biUnion id) hTail
          rw [Finset.biUnion_insert]
          exact hBoth
        · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
          subst T
          simpa using hT B (by simp)
  have hC : C ∈ F := by
    exact hbiUnion_mem S hS_mem ⟨A, hA_S⟩
  have hAsub : A ⊆ C := by
    intro y hy
    apply Finset.mem_biUnion.mpr
    exact ⟨A, hA_S, hy⟩
  have hupper : C ∪ (A ∪ {x}) ∈ F :=
    hUnion C hC (A ∪ {x}) hAx
  have hupper' : C ∪ {x} ∈ F := by
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr hAsub] at hupper
    exact hupper
  have hnotx : x ∉ C := by
    intro hxC
    rcases Finset.mem_biUnion.mp hxC with ⟨B, hB, hxB⟩
    exact (Finset.mem_filter.mp hB).2 hxB
  simpa [S, C] using And.intro hC (And.intro hupper' hnotx)

end MathlibPlus.Combinatorics.CanonicalCollision
