import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The direct product `S₃ × A₄` has a connected valency-ten ordinary Cayley CI defect. -/
def symmetricThreeAlternatingFourConnectedValencyTenCIDefect : Prop :=
  let G := Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)
  ∃ (S T : Set G) (e : G ≃ G),
    S = S⁻¹ ∧ T = T⁻¹ ∧
    (1 : G) ∉ S ∧ (1 : G) ∉ T ∧
    S.ncard = 10 ∧ T.ncard = 10 ∧
    Subgroup.closure S = ⊤ ∧ Subgroup.closure T = ⊤ ∧
    e 1 = 1 ∧ (∀ x : G, e (e x) = x) ∧
    (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
    ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
