import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Restriction of a permutation that stabilizes a set to that set. -/
def restrictPermutation {α : Type*} (x : Equiv.Perm α)
    (B : Set α) (hB : x '' B = B) : Equiv.Perm B :=
  Equiv.ofBijective
    (fun y : B =>
      ⟨x y.1, by
        have hy : x y.1 ∈ x '' B := ⟨y.1, y.2, rfl⟩
        rw [hB] at hy
        exact hy⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact x.injective (congrArg Subtype.val hab), by
      intro y
      have hy : y.1 ∈ x '' B := by
        rw [hB]
        exact y.2
      rcases hy with ⟨z, hz, hzy⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      exact Subtype.ext hzy⟩

/-- A permutation set is transitive when it moves every point to every other point. -/
def permutationSetTransitive {α : Type*} (H : Set (Equiv.Perm α)) : Prop :=
  ∀ a b : α, ∃ h ∈ H, h a = b

/-- A nonempty block for a set of permutations. -/
def permutationSetBlock {α : Type*} (H : Set (Equiv.Perm α)) (B : Set α) : Prop :=
  B.Nonempty ∧ ∀ h ∈ H, h '' B = B ∨ Disjoint (h '' B) B

/-- A partition into nonempty blocks invariant under a permutation set. -/
def permutationSetBlockSystem {α : Type*}
    (H : Set (Equiv.Perm α)) (𝓑 : Set (Set α)) : Prop :=
  (∀ B ∈ 𝓑, permutationSetBlock H B) ∧
    (∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
    ⋃₀ 𝓑 = Set.univ

/-- The singleton-block partition predicate. -/
def singletonBlockSystem {α : Type*} (𝓑 : Set (Set α)) : Prop :=
  ∀ B, B ∈ 𝓑 ↔ ∃ a : α, B = {a}

/-- A primitive permutation set is transitive and has only the two trivial invariant partitions. -/
def primitivePermutationSet {α : Type*} (H : Set (Equiv.Perm α)) : Prop :=
  permutationSetTransitive H ∧
    ∀ 𝓑 : Set (Set α), permutationSetBlockSystem H 𝓑 →
      𝓑 = {Set.univ} ∨ singletonBlockSystem 𝓑

/-- Proper refinement of a partition by another family of blocks. -/
def properBlockRefinement {α : Type*}
    (𝓑₁ 𝓑₂ : Set (Set α)) : Prop :=
  (∀ B₁ ∈ 𝓑₁, ∃ B₂ ∈ 𝓑₂, B₁ ⊆ B₂) ∧ 𝓑₁ ≠ 𝓑₂

/-- Minimality among nontrivial block systems, using proper refinement. -/
def minimumNontrivialBlockSystem {α : Type*}
    (X : Set (Equiv.Perm α)) (𝓑 : Set (Set α)) : Prop :=
  permutationSetBlockSystem X 𝓑 ∧
    𝓑 ≠ {Set.univ} ∧
    ¬ singletonBlockSystem 𝓑 ∧
    ∀ 𝓒 : Set (Set α), permutationSetBlockSystem X 𝓒 →
      𝓒 ≠ {Set.univ} → ¬ singletonBlockSystem 𝓒 →
      ¬ properBlockRefinement 𝓒 𝓑

/-- Permutations induced on a block by its setwise stabilizer. -/
def inducedLocalPermutations {α : Type*}
    (X : Set (Equiv.Perm α)) (B : Set α) : Set (Equiv.Perm B) :=
  {h | ∃ x ∈ X, ∃ hx : x '' B = B,
    h = restrictPermutation x B hx}

/-- Claim 37201: a minimum nontrivial global block system has primitive local action. -/
def minimumBlockSystemInducesPrimitiveLocalAction
    {α : Type*} (X : Subgroup (Equiv.Perm α))
    (𝓑 : Set (Set α)) (B : Set α) : Prop :=
  permutationSetTransitive (X : Set (Equiv.Perm α)) ∧
    minimumNontrivialBlockSystem (X : Set (Equiv.Perm α)) 𝓑 ∧
    B ∈ 𝓑 →
      primitivePermutationSet (inducedLocalPermutations
        (X : Set (Equiv.Perm α)) B)

end

end MathlibPlus.Open.ResearchFormalization
