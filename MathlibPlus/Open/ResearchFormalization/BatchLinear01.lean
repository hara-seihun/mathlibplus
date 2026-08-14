import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Fixed-base matrix-layer shadow, including the transport-block conclusion. -/
def claim59238 : Prop :=
  ∀ (p : ℕ),
    2 < p →
    Nat.Prime p →
    ∀ (X : Type*) [AddCommGroup X] [Finite X]
      [Module (ZMod p) X] [Module.Finite (ZMod p) X],
      ∀ (L : ZMod p → X ≃ₗ[ZMod p] X),
        let Y := X × ZMod p
        let q : Y → Y := fun z => (L z.2 z.1, z.2)
        let qInv : Y → Y := fun z => ((L z.2).symm z.1, z.2)
        let τ : Y → Y → Y := fun v s => qInv (q (v + s) - q v)
        let baseRel : Y → Y → Prop :=
          fun s t => (∃ v : Y, t = τ v s) ∨ t = -s
        let block : Y → Set Y :=
          fun a => {b : Y | Relation.EqvGen baseRel a b}
        let blocks : Set (Set Y) :=
          {B : Set Y | ∃ a : Y, B = block a}
        let l0 : Y → Y := fun z => (L 0 z.1, z.2)
        (∀ B : Set Y, B ∈ blocks → Set.image q B = Set.image l0 B) ∧
        ∀ S : Set Y,
          (∀ s : Y, s ∈ S → block s ⊆ S) →
          (∀ s : Y, s ∈ S → -s ∈ S) →
          Function.Bijective q ∧
          (∀ x y : Y,
            y - x ∈ S ↔ q y - q x ∈ Set.image l0 S)

end MathlibPlus.Open.ResearchFormalization
