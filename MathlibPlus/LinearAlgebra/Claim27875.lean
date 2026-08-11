import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 27875: exact displacement identity over the finite field `ZMod p`. -/
theorem claim27875_orbitalDisplacement
    (p : ℕ) [Fact p.Prime] (i j r s : ZMod p) :
    let F : (ZMod p × ZMod p) → (Fin 3 → ZMod p) :=
      fun u => ![u.1 * (u.1 - 1), (2 * u.1 - 1) * u.2, u.2 ^ 2]
    let d₁ : Fin 3 → ZMod p := ![i, j, 0]
    let d₂ : Fin 3 → ZMod p := ![0, i, j]
    let W : Submodule (ZMod p) (Fin 3 → ZMod p) :=
      Submodule.span (ZMod p) ({d₁, d₂} : Set (Fin 3 → ZMod p))
    F ((r, s) + (i, j)) - F (r, s) =
        (2 * r + i - 1) • d₁ + (2 * s + j) • d₂ ∧
      F ((r, s) + (i, j)) - F (r, s) ∈ W := by
  dsimp
  have hformula :
      (![((r + i) * (r + i - 1)),
        ((2 * (r + i) - 1) * (s + j)),
        ((s + j) ^ 2)] : Fin 3 → ZMod p) -
        ![r * (r - 1), (2 * r - 1) * s, s ^ 2] =
        (2 * r + i - 1) • ![i, j, 0] +
          (2 * s + j) • ![0, i, j] := by
    funext k
    fin_cases k <;> simp
    all_goals ring
  constructor
  · exact hformula
  · rw [hformula]
    apply Submodule.add_mem
    · exact (Submodule.span (ZMod p) ({![i, j, 0], ![0, i, j]} : Set (Fin 3 → ZMod p))).smul_mem _
        (Submodule.subset_span (by simp))
    · exact (Submodule.span (ZMod p) ({![i, j, 0], ![0, i, j]} : Set (Fin 3 → ZMod p))).smul_mem _
        (Submodule.subset_span (by simp))

end MathlibPlus.LinearAlgebra
