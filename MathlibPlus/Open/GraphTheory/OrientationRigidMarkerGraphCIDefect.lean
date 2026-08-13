import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- An odd-order marker group whose second marked inverse-pair has no
orientation-reversing stabilizer transfers the binary directed `A₄` defect to
an inverse-closed valency-twelve Cayley-graph defect. -/
def orientationRigidMarkerProducesValencyTwelveGraphCIDefect : Prop :=
  ∀ (H : Type*) [Finite H] [Group H] (r s : H),
    r ≠ r⁻¹ →
    s ≠ s⁻¹ →
    ({r, r⁻¹} : Set H) ∩ {s, s⁻¹} = ∅ →
    Nat.Coprime (Nat.card H) 12 →
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
      e 1 = 1 ∧
      Function.Involutive e ∧
      (∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
      ∀ φ : (H × alternatingGroup (Fin 4)) ≃*
          (H × alternatingGroup (Fin 4)),
        φ '' S ≠ T

end MathlibPlus.Open.GraphTheory
