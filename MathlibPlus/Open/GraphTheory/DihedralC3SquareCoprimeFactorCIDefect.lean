import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Cell P1: multiplying `Dih(C₃²)` by any nontrivial finite group of order
coprime to `18` produces a valency-nine ordinary undirected Cayley CI defect. -/
def dihedralC3SquareNontrivialCoprimeFactorValencyNineCIDefect : Prop :=
  let A := Multiplicative (ZMod 3 × ZMod 3)
  let C := Multiplicative (ZMod 2)
  (∃ φ : C →* MulAut A,
      ∀ a : A, φ (.ofAdd 1) a = a⁻¹) ∧
  ∀ (φ : C →* MulAut A),
    (∀ a : A, φ (.ofAdd 1) a = a⁻¹) →
    ∀ (K : Type*) [Finite K] [Group K],
      Nat.Coprime (Nat.card K) 18 →
      1 < Nat.card K →
      let H := A ⋊[φ] C
      let G := H × K
      Nat.card G = 18 * Nat.card K ∧
      ∃ (S T : Set G) (e : G ≃ G),
        S = S⁻¹ ∧
        T = T⁻¹ ∧
        1 ∉ S ∧
        1 ∉ T ∧
        S.ncard = 9 ∧
        T.ncard = 9 ∧
        e 1 = 1 ∧
        Function.Involutive e ∧
        (∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
        ∀ α : G ≃* G, α '' S ≠ T

end MathlibPlus.Open.GraphTheory
