import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Five is the sharp minimum valency of a connected ordinary Cayley CI defect on `Q₈ × S₃`. -/
def quaternionEightSymmetricThreeSharpConnectedCIDefectValency : Prop :=
  let G := QuaternionGroup 2 × Equiv.Perm (Fin 3)
  (∃ (S T : Set G) (e : G ≃ G),
    S = S⁻¹ ∧ T = T⁻¹ ∧
    (1 : G) ∉ S ∧ (1 : G) ∉ T ∧
    S.ncard = 5 ∧ T.ncard = 5 ∧
    Subgroup.closure S = ⊤ ∧ Subgroup.closure T = ⊤ ∧
    e 1 = 1 ∧ (∀ x : G, e (e x) = x) ∧
    (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
    ¬ ∃ α : G ≃* G, α '' S = T) ∧
  ∀ (S T : Set G),
    S = S⁻¹ → T = T⁻¹ →
    (1 : G) ∉ S → (1 : G) ∉ T →
    Subgroup.closure S = ⊤ → Subgroup.closure T = ⊤ →
    S.ncard < 5 → T.ncard = S.ncard →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
    ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
