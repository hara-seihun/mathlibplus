import Mathlib

namespace MathlibPlus.Open
namespace R5339

/-- The admitted `R-5339#reconcile-1` claim. -/
def claim60500 : Prop :=
  ∀ (p : ℕ), p.Prime ∧ Odd p ∧ 5 ≤ p →
    let A := Fin 3 → ZMod p
    let B := Fin 3 → ZMod p
    let e₁ : B := ![1, 0, 0]
    let e₂ : B := ![0, 1, 0]
    let e₃ : B := ![0, 0, 1]
    let F : B → A := fun z =>
      ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]
    let P : Set B :=
      {e₁, -e₁, e₂, -e₂, e₃, -e₃, e₂ + e₃, -(e₂ + e₃)}
    let W : B → Submodule (ZMod p) A := fun d =>
      Submodule.span (ZMod p) {v | d ∈ P ∧ ∃ x : B,
        v = F (x + d) - F x - F d ∨
        v = F (x - d) - F x - F (-d)}
    W e₁ = Submodule.span (ZMod p) {e₁} ∧
    W (-e₁) = Submodule.span (ZMod p) {e₁} ∧
    W e₂ = Submodule.span (ZMod p) {e₁, e₂} ∧
    W (-e₂) = Submodule.span (ZMod p) {e₁, e₂} ∧
    W e₃ = Submodule.span (ZMod p) {e₁, e₃} ∧
    W (-e₃) = Submodule.span (ZMod p) {e₁, e₃} ∧
    W (e₂ + e₃) = ⊤ ∧
    W (-(e₂ + e₃)) = ⊤

end R5339
end MathlibPlus.Open
