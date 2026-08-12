import Mathlib

namespace MathlibPlus.Combinatorics.Claim5950

/-- A map preserving every orbital preserves arbitrary directed unions of those
orbitals, and also arbitrary unions in which each orbital is paired with its
inverse. -/
theorem directedAndInversePairedOrbitalUnionsPreserved
    {α ι : Type*} (q : α → α) (O : ι → Set (α × α)) (I : Set ι)
    (hO : ∀ i, Prod.map q q '' O i = O i) :
    Prod.map q q '' (⋃ i : ι, ⋃ _ : i ∈ I, O i) =
        (⋃ i : ι, ⋃ _ : i ∈ I, O i) ∧
    Prod.map q q ''
          (⋃ i : ι, ⋃ _ : i ∈ I,
            (O i ∪ (fun p : α × α => (p.2, p.1)) '' O i)) =
        (⋃ i : ι, ⋃ _ : i ∈ I,
          (O i ∪ (fun p : α × α => (p.2, p.1)) '' O i)) := by
  let Q : α × α → α × α := Prod.map q q
  let swap : α × α → α × α := fun p => (p.2, p.1)
  have hQ : ∀ i, Q '' O i = O i := by
    intro i
    exact hO i
  have union_preserved : ∀ (F : ι → Set (α × α)),
      (∀ i, Q '' F i = F i) →
        Q '' (⋃ i : ι, ⋃ _ : i ∈ I, F i) =
          (⋃ i : ι, ⋃ _ : i ∈ I, F i) := by
    intro F hF
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hi, hx⟩
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
      exact (hF i) ▸ ⟨x, hx, rfl⟩
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
      rcases Set.mem_iUnion.mp hp with ⟨hi, hp⟩
      have hp' : p ∈ Q '' F i := by
        rw [hF i]
        exact hp
      rcases hp' with ⟨x, hx, rfl⟩
      exact ⟨x, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩, rfl⟩
  have hSwap (i : ι) : Q '' (swap '' O i) = swap '' O i := by
    calc
      Q '' (swap '' O i) = (Q ∘ swap) '' O i := by
        simpa only [Function.comp_apply] using (Set.image_image Q swap (O i))
      _ = (swap ∘ Q) '' O i := by
        congr 1
      _ = swap '' (Q '' O i) := by
        simpa only [Function.comp_apply] using (Set.image_image swap Q (O i)).symm
      _ = swap '' O i := by rw [hQ i]
  have hPair : ∀ i, Q '' (O i ∪ swap '' O i) = O i ∪ swap '' O i := by
    intro i
    rw [Set.image_union, hQ i, hSwap i]
  have hdirect := union_preserved O hQ
  have hpaired := union_preserved (fun i => O i ∪ swap '' O i) hPair
  simpa [Q, swap] using And.intro hdirect hpaired

end MathlibPlus.Combinatorics.Claim5950
