import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Arbitrary normalized vertical layer shears on scalar prime-square
semidirect products by `C₃` have one group-automorphism shadow on every
compatible family of directed Cayley connection sets. -/
def scalarPrimeSquareArbitraryVerticalLayerShearsHaveUniversalAutomorphismShadow : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ ω : ZMod p,
    ω ^ 3 = 1 → ω ≠ 1 →
    (∃ action : Multiplicative (ZMod 3) →*
        MulAut (Multiplicative (ZMod p × ZMod p)),
      ∀ v : Multiplicative (ZMod p × ZMod p),
        action (.ofAdd 1) v =
          .ofAdd (ω * v.toAdd.1, ω * v.toAdd.2)) ∧
    ∀ action : Multiplicative (ZMod 3) →*
        MulAut (Multiplicative (ZMod p × ZMod p)),
      (∀ v : Multiplicative (ZMod p × ZMod p),
        action (.ofAdd 1) v =
          .ofAdd (ω * v.toAdd.1, ω * v.toAdd.2)) →
      let G := Multiplicative (ZMod p × ZMod p) ⋊[action]
        Multiplicative (ZMod 3)
      ∀ h : ZMod 3 → ZMod p → ZMod p, h 0 0 = 0 →
        let qFun : G → G := fun g =>
          (⟨.ofAdd (g.left.toAdd.1,
            g.left.toAdd.2 + h g.right.toAdd g.left.toAdd.1),
            g.right⟩ : G)
        (∃ q : G ≃ G, ∀ g, q g = qFun g) ∧
        ∀ q : G ≃ G, (∀ g, q g = qFun g) →
          ∃ α : G ≃* G,
            ∀ S T : Set G,
              (∀ x y, x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
              α '' S = T

end MathlibPlus.Open.GraphTheory
