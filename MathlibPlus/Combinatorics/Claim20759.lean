import Mathlib

namespace MathlibPlus.Combinatorics.Claim20759

/-- The union of all members omitting an actual coordinate is itself a member of a
finite union-closed family, omits that coordinate, and contains every such member. -/
theorem canonicalMaximalMemberOmittingCoordinate
    {X : Type*} [DecidableEq X]
    (F : Finset (Finset X))
    (hUnion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (x : X)
    (hOmitted : ∃ A, A ∈ F ∧ x ∉ A) :
    let C := (F.filter (fun A => x ∉ A)).biUnion id
    C ∈ F ∧ x ∉ C ∧ ∀ A ∈ F, x ∉ A → A ⊆ C := by
  classical
  let S : Finset (Finset X) := F.filter (fun A => x ∉ A)
  let C : Finset X := S.biUnion id
  have hS_mem : ∀ B ∈ S, B ∈ F := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hS_nonempty : S.Nonempty := by
    rcases hOmitted with ⟨A, hA, hxA⟩
    exact ⟨A, by simp [S, hA, hxA]⟩
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
    exact hbiUnion_mem S hS_mem hS_nonempty
  have hnotx : x ∉ C := by
    intro hxC
    rcases Finset.mem_biUnion.mp hxC with ⟨B, hB, hxB⟩
    exact (Finset.mem_filter.mp hB).2 hxB
  have hsubset : ∀ A ∈ F, x ∉ A → A ⊆ C := by
    intro A hA hxA y hy
    apply Finset.mem_biUnion.mpr
    exact ⟨A, by simp [S, hA, hxA], hy⟩
  simpa [S, C] using And.intro hC (And.intro hnotx hsubset)

end MathlibPlus.Combinatorics.Claim20759
