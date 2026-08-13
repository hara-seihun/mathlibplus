import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every reduced nonlinear monomial layer shear is harmless for directed
Cayley connection sets on scalar prime-square semidirect products by `C₃`. -/
def scalarPrimeSquareReducedMonomialLayerShearsFixCayleyConnectionSets : Prop :=
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
      ∀ d : ℕ, 2 ≤ d → d < p →
      ∀ a : ZMod 3 → ZMod p,
        let qFun : G → G := fun g =>
          (⟨.ofAdd (g.left.toAdd.1,
            g.left.toAdd.2 + a g.right.toAdd * g.left.toAdd.1 ^ d),
            g.right⟩ : G)
        (∃ q : G ≃ G, ∀ g, q g = qFun g) ∧
        ∀ q : G ≃ G, (∀ g, q g = qFun g) →
          ∀ S T : Set G,
            (∀ x y, x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
            q '' S = S ∧ T = S

end MathlibPlus.Open.GraphTheory
