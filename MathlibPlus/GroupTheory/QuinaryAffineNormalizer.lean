import Mathlib

namespace MathlibPlus.GroupTheory

/-- The affine permutations of the five-element field are exactly the
finite normalizer condition for the regular translation cycle, and have
cardinality 20; the complement has cardinality 100. -/
theorem quinaryAffineNormalizerCensus :
    let ρ : Equiv.Perm (ZMod 5) := Equiv.addRight 1
    let normalizer : Equiv.Perm (ZMod 5) → Prop :=
      fun σ => ∀ k : Fin 5, ∃ l : Fin 5,
        σ * ρ ^ (k : ℕ) * σ⁻¹ = ρ ^ (l : ℕ)
    let affine : Equiv.Perm (ZMod 5) → Prop :=
      fun σ => ∃ a b : ZMod 5, a ≠ 0 ∧ ∀ x, σ x = a * x + b
    (∀ σ, normalizer σ ↔ affine σ) ∧
      Fintype.card {σ : Equiv.Perm (ZMod 5) // affine σ} = 20 ∧
      Fintype.card {σ : Equiv.Perm (ZMod 5) // ¬affine σ} = 100 := by
  dsimp
  native_decide

end MathlibPlus.GroupTheory
