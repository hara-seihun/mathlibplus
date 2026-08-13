import Mathlib

namespace MathlibPlus.Combinatorics.Claim21762

/-- A nonempty finite union-closed family of finite sets contains its union,
which is the unique inclusion-maximum member. -/
theorem union_mem_unique_max
    {α : Type*} [DecidableEq α]
    (H : Finset (Finset α))
    (hne : H.Nonempty)
    (hunion : ∀ A ∈ H, ∀ B ∈ H, A ∪ B ∈ H) :
    H.biUnion id ∈ H ∧
      (∀ A ∈ H, A ⊆ H.biUnion id) ∧
      (∀ M, M ∈ H → (∀ A ∈ H, A ⊆ M) → M = H.biUnion id) := by
  classical
  have hbiUnion_mem : ∀ T : Finset (Finset α),
      (∀ B ∈ T, B ∈ H) → T.Nonempty → T.biUnion id ∈ H := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _ hneT
        exact False.elim (by simpa using hneT)
    | @insert B T hB ih =>
        intro hT hneT
        by_cases hTne : T.Nonempty
        · have hTail : T.biUnion id ∈ H :=
            ih (fun D hD => hT D (Finset.mem_insert_of_mem hD)) hTne
          have hBoth := hunion B (hT B (Finset.mem_insert_self B T))
            (T.biUnion id) hTail
          rw [Finset.biUnion_insert]
          exact hBoth
        · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
          subst T
          simpa using hT B (by simp)
  have hτ_mem : H.biUnion id ∈ H :=
    hbiUnion_mem H (fun B hB => hB) hne
  have hτ_upper : ∀ A ∈ H, A ⊆ H.biUnion id := by
    intro A hA
    exact Finset.subset_biUnion_of_mem id hA
  refine ⟨hτ_mem, hτ_upper, ?_⟩
  intro M hM hMupper
  exact Finset.Subset.antisymm (hτ_upper M hM) (hMupper _ hτ_mem)

end MathlibPlus.Combinatorics.Claim21762
