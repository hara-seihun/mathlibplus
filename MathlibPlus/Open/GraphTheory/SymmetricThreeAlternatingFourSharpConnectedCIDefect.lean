import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

namespace MathlibPlus.Open.GraphTheory

/-- Five is the least valency of a connected ordinary Cayley CI defect on
`S₃ × A₄`. -/
def symmetricThreeAlternatingFourSharpConnectedCIDefectValencyFive : Prop :=
  let G := Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)
  (∀ (U V : Set G),
      U = U⁻¹ → V = V⁻¹ →
      (1 : G) ∉ U → (1 : G) ∉ V →
      U.ncard < 5 →
      Subgroup.closure U = ⊤ → Subgroup.closure V = ⊤ →
      (∃ e : G ≃ G,
        ∀ x y : G, x⁻¹ * y ∈ U ↔ (e x)⁻¹ * e y ∈ V) →
      ∃ α : G ≃* G, α '' U = V) ∧
  ∃ (S T : Set G) (e : G ≃ G),
    S = S⁻¹ ∧ T = T⁻¹ ∧
    (1 : G) ∉ S ∧ (1 : G) ∉ T ∧
    S.ncard = 5 ∧ T.ncard = 5 ∧
    Subgroup.closure S = ⊤ ∧ Subgroup.closure T = ⊤ ∧
    e 1 = 1 ∧
    (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
    ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
