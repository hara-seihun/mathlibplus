import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim42222

/-- The finite transition counterexample from claim 42222.  The matrix
minor convention is explicit: columns `(j,k)` contribute
`T 0 j * T 1 k - T 0 k * T 1 j`. -/
theorem strict_tn_transition_counterexample_claim42222 :
    let T₁ : Matrix (Fin 2) (Fin 3) ℤ := !![1, 2, 3; 1, 3, 5]
    let r₁ : Fin 2 → ℤ := ![1, 10]
    let r₂ : Fin 3 → ℤ := fun j => ∑ i : Fin 2, r₁ i * T₁ i j
    let minor : Fin 3 → Fin 3 → ℤ :=
      fun j k => T₁ 0 j * T₁ 1 k - T₁ 0 k * T₁ 1 j
    let stacked : Matrix (Fin 2) (Fin 2) ℤ := !![r₁ 0, r₁ 1; r₂ 0, r₂ 1]
    minor 0 1 = 1 ∧ minor 0 2 = 2 ∧ minor 1 2 = 1 ∧
      r₂ = ![11, 32, 53] ∧ Matrix.det stacked = -78 := by
  dsimp
  have hr₂ : (fun j : Fin 3 => ∑ i : Fin 2, (![1, 10] : Fin 2 → ℤ) i *
      (!![1, 2, 3; 1, 3, 5] : Matrix (Fin 2) (Fin 3) ℤ) i j) =
      (![11, 32, 53] : Fin 3 → ℤ) := by
    funext j
    fin_cases j <;> norm_num [Fin.sum_univ_two]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · exact hr₂
  · rw [Matrix.det_fin_two]
    norm_num

end MathlibPlus.LinearAlgebra.Claim42222
