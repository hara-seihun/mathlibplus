import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Cell P1: for every prime `p ≥ 5`, the coprime direct product
`Dih(C₉) × C_p` has a connected valency-nine ordinary undirected Cayley
CI defect. -/
def dihedralCyclicNineCyclicPrimeConnectedValencyNineCIDefect : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    let A := Multiplicative (ZMod 9)
    let C := Multiplicative (ZMod 2)
    (∃ φ : C →* MulAut A,
        ∀ a : A, φ (.ofAdd 1) a = a⁻¹) ∧
    ∀ (φ : C →* MulAut A),
      (∀ a : A, φ (.ofAdd 1) a = a⁻¹) →
      let H := A ⋊[φ] C
      let G := H × Multiplicative (ZMod p)
      Nat.card G = 18 * p ∧
      ∃ (S T : Set G) (e : G ≃ G),
        S = S⁻¹ ∧
        T = T⁻¹ ∧
        1 ∉ S ∧
        1 ∉ T ∧
        S.ncard = 9 ∧
        T.ncard = 9 ∧
        Subgroup.closure S = ⊤ ∧
        Subgroup.closure T = ⊤ ∧
        e 1 = 1 ∧
        Function.Involutive e ∧
        (∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
        ∀ α : G ≃* G, α '' S ≠ T

end MathlibPlus.Open.GraphTheory
