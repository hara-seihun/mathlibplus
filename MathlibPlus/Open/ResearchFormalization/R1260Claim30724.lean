import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchR1260

namespace MathlibPlus.Open.ResearchFormalization.R1260Claim30724

/-- On every common `p`-point block in the Records 2--3 setting, the three
induced permutation groups are the same. -/
def claim30724 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 13 ≤ p →
    ∀ (U B : Type*) [Group U] [Finite U] [Fintype B]
      [MulAction U B] (P Q : Subgroup U),
      IsPGroup p U →
      Nat.card B = p →
      Subgroup.closure ((P : Set U) ∪ (Q : Set U)) = ⊤ →
      Nat.card P = p →
      Nat.card Q = p →
      Nat.card
          (MathlibPlus.Open.Research.inducedPermGroup
            (U := U) (B := B) P) = p →
      Nat.card
          (MathlibPlus.Open.Research.inducedPermGroup
            (U := U) (B := B) Q) = p →
      MathlibPlus.Open.Research.actsTransitivelyOn
        (U := U) (B := B) P →
      MathlibPlus.Open.Research.actsTransitivelyOn
        (U := U) (B := B) Q →
      MathlibPlus.Open.Research.inducedPermGroup
          (U := U) (B := B) P =
        MathlibPlus.Open.Research.inducedPermGroup
          (U := U) (B := B) (⊤ : Subgroup U) ∧
      MathlibPlus.Open.Research.inducedPermGroup
          (U := U) (B := B) (⊤ : Subgroup U) =
        MathlibPlus.Open.Research.inducedPermGroup
          (U := U) (B := B) Q

end MathlibPlus.Open.ResearchFormalization.R1260Claim30724
