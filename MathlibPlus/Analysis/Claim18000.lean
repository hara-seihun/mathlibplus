import Mathlib

namespace MathlibPlus.Analysis

open scoped BigOperators

/-- The standard Julia reflection matrix is a symmetric orthogonal
involution with determinant `-1`; the particular Gudermannian parameterization
is irrelevant to this algebraic fact. -/
theorem juliaReflection_orthogonal_claim18000 (gd : ℝ → ℝ) :
    let juliaReflection : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun θ =>
      !![Real.cos θ, Real.sin θ; Real.sin θ, -Real.cos θ]
    let U : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ξ => juliaReflection (gd ξ)
    ∀ ξ : ℝ,
      Matrix.transpose (U ξ) = U ξ ∧
      Matrix.transpose (U ξ) * U ξ = 1 ∧
      U ξ * U ξ = 1 ∧
      Matrix.det (U ξ) = -1 := by
  dsimp
  intro ξ
  let c : ℝ := Real.cos (gd ξ)
  let s : ℝ := Real.sin (gd ξ)
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![c, s; s, -c]
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    simpa [add_comm] using Real.sin_sq_add_cos_sq (gd ξ)
  have hsymm : Matrix.transpose M = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M]
  have hsq : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith [hcs]
  have hdet : Matrix.det M = -1 := by
    rw [Matrix.det_fin_two]
    simp [M]
    nlinarith [hcs]
  have hord : Matrix.transpose M * M = 1 := by rw [hsymm, hsq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [M, c, s] using hsymm
  · simpa [M, c, s] using hord
  · simpa [M, c, s] using hsq
  · simpa [M, c, s] using hdet

end MathlibPlus.Analysis
