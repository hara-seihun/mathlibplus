import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/--
Rank characterization of a pointed block circuit at a target coordinate.
The row blocks are represented by pairwise-disjoint subsets whose union is all rows.
-/
def pointedBlockCircuitRankCharacterization
    {F R S B : Type*}
    [Field F] [Fintype R] [Fintype S] [Fintype B]
    (A : Matrix R S F)
    (rowBlock : B → Set R)
    (hrowPartition :
      (∀ ⦃b₁ b₂ : B⦄, b₁ ≠ b₂ → Disjoint (rowBlock b₁) (rowBlock b₂)) ∧
        (⋃ b, rowBlock b = Set.univ))
    (t : S) : Prop := by
  classical
  exact
    let rowVector : R → (S → F) := fun r s => A r s
    let blockSpace : B → Submodule F (S → F) :=
      fun b => Submodule.span F (rowVector '' rowBlock b)
    let unionSpace : Finset B → Submodule F (S → F) :=
      fun J => J.sup blockSpace
    let targetLine : Submodule F (S → F) :=
      Submodule.span F {Pi.single t (1 : F)}
    let properSubset : Finset B → Finset B → Prop :=
      fun I J => I ⊆ J ∧ I ≠ J
    ∀ J : Finset B,
      (targetLine ≤ unionSpace J ∧
          ∀ I : Finset B, properSubset I J → ¬ targetLine ≤ unionSpace I) ↔
        (Module.finrank F ↥(unionSpace J ⊔ targetLine) =
            Module.finrank F ↥(unionSpace J) ∧
          ∀ I : Finset B, properSubset I J →
            Module.finrank F ↥(unionSpace I ⊔ targetLine) =
              Module.finrank F ↥(unionSpace I) + 1)

end MathlibPlus.Open.LinearAlgebra
