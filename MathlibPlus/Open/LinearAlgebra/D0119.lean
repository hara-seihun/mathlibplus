import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- A block-minimal delta certificate on the active coordinate carrier `S`. -/
def claim5637 {𝕜 : Type*} [Field 𝕜]
    {m n q : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    (block : Fin m → Fin q)
    (S : Finset (Fin n)) (t : Fin n) (J : Finset (Fin q)) : Prop :=
  Function.Surjective block ∧
  ∃ (ht : t ∈ S),
    let rowSpan : Fin q → Submodule 𝕜 (S → 𝕜) := fun b =>
      Submodule.span 𝕜 (Set.range (fun i : {i : Fin m // block i = b} =>
        fun c : S => A i.1 c.1))
    let delta : S → 𝕜 := Pi.single ⟨t, ht⟩ 1
    let spans : Finset (Fin q) → Prop := fun T =>
      ∃ (u : {b // b ∈ T} → S → 𝕜) (a : 𝕜),
        a ≠ 0 ∧
        (∀ b, u b ∈ rowSpan b.1) ∧
        (∑ b : {b // b ∈ T}, u b) = a • delta
    spans J ∧ ∀ T : Finset (Fin q), T ⊂ J → ¬ spans T

end MathlibPlus.Open.LinearAlgebra
