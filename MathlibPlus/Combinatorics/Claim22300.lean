import Mathlib

namespace MathlibPlus.Combinatorics

/-- Set-theoretic form of the exclusive-gap argument.  The strict inclusions
make each gap nonempty, while the stated containment of a gap in its own
block makes distinct gaps disjoint. -/
theorem exclusive_gaps_nonempty_pairwise_disjoint_claim22300
    {α ι : Type*}
    (U : Set α) (B : ι → Set α)
    (hproper : ∀ i : ι,
      (⋃ j : ι, ⋃ (_ : j ≠ i), B j) ⊂ U)
    (hsubset : ∀ i : ι,
      U \ (⋃ j : ι, ⋃ (_ : j ≠ i), B j) ⊆ B i) :
    let E : ι → Set α := fun i =>
      U \ (⋃ j : ι, ⋃ (_ : j ≠ i), B j)
    (∀ i, (E i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) := by
  let E : ι → Set α := fun i =>
    U \ (⋃ j : ι, ⋃ (_ : j ≠ i), B j)
  change (∀ i, (E i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (E i) (E j))
  constructor
  · intro i
    dsimp [E]
    exact (Set.ssubset_iff_exists.mp (hproper i)).2
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hxjB : x ∈ B j := hsubset j hxj
    have hxnot : x ∉ ⋃ k : ι, ⋃ (_ : k ≠ i), B k := (show x ∈ E i from hxi).2
    apply hxnot
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    refine Set.mem_iUnion.2 ⟨Ne.symm hij, hxjB⟩

end MathlibPlus.Combinatorics
