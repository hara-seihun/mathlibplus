import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Cell X1: the semidirect product of the binary two-dimensional vector group
by the cyclic group of order nine, with the action factoring through a
fixed-point-free order-three action, is an ordinary undirected CI-group. -/
def c2SquareSemidirectCyclicNineUndirectedCI : Prop :=
  let V := Multiplicative (Fin 2 → ZMod 2)
  let C := Multiplicative (ZMod 9)
  (∃ φ : C →* MulAut V,
      ∀ v : V, φ (.ofAdd 1) v = v → v = 1) ∧
  ∀ (φ : C →* MulAut V),
    (∀ v : V, φ (.ofAdd 1) v = v → v = 1) →
    let G := V ⋊[φ] C
    Nat.card G = 36 ∧
    Nat.card (Subgroup.center G) = 3 ∧
    ∀ (S T : Set G),
      1 ∉ S → 1 ∉ T →
      (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
      (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
      (∃ e : G ≃ G, ∀ x y : G,
        x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
