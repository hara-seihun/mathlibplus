import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- A generating orientation-rigid marker transfers the binary directed `A₄`
defect to a connected inverse-closed valency-twelve Cayley-graph defect. -/
def orientationRigidGeneratingMarkerProducesConnectedValencyTwelveGraphCIDefect : Prop :=
  ∀ (H : Type*) [Finite H] [Group H] (r s : H),
    r ≠ r⁻¹ →
    s ≠ s⁻¹ →
    ({r, r⁻¹} : Set H) ∩ {s, s⁻¹} = ∅ →
    Nat.Coprime (Nat.card H) 12 →
    Subgroup.closure ({r, s} : Set H) = ⊤ →
    (∀ θ : H ≃* H,
      θ '' ({r, r⁻¹} : Set H) = {r, r⁻¹} →
      θ '' ({s, s⁻¹} : Set H) = {s, s⁻¹} →
      θ s = s) →
    ∃ (S T : Set (H × alternatingGroup (Fin 4)))
        (e : (H × alternatingGroup (Fin 4)) ≃
          (H × alternatingGroup (Fin 4))),
      S = S⁻¹ ∧
      T = T⁻¹ ∧
      1 ∉ S ∧
      1 ∉ T ∧
      S.ncard = 12 ∧
      T.ncard = 12 ∧
      Subgroup.closure S = ⊤ ∧
      Subgroup.closure T = ⊤ ∧
      e 1 = 1 ∧
      Function.Involutive e ∧
      (∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
      ∀ φ : (H × alternatingGroup (Fin 4)) ≃*
          (H × alternatingGroup (Fin 4)),
        φ '' S ≠ T

end MathlibPlus.Open.GraphTheory
