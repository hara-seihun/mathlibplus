import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- A nonabelian orientation tag produces a connected ordinary Cayley-graph
CI defect on `(C₇ ⋊₂ C₃) × A₄`. -/
def alternatingFourFrobeniusTwentyOneConnectedUndirectedCIDefect : Prop :=
  ∃ ρ : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7)),
    (∀ x : ZMod 7,
      ρ (Multiplicative.ofAdd (1 : ZMod 3)) (Multiplicative.ofAdd x) =
        Multiplicative.ofAdd (2 * x)) ∧
    let H := Multiplicative (ZMod 7) ⋊[ρ] Multiplicative (ZMod 3)
    let G := H × alternatingGroup (Fin 4)
    ∃ (S T : Set G) (e : G ≃ G),
      S = S⁻¹ ∧ T = T⁻¹ ∧
      (1 : G) ∉ S ∧ (1 : G) ∉ T ∧
      S.ncard = 12 ∧ T.ncard = 12 ∧
      Subgroup.closure S = ⊤ ∧ Subgroup.closure T = ⊤ ∧
      e 1 = 1 ∧ (∀ x : G, e (e x) = x) ∧
      (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
      ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
