import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12841

/-- The explicit rank-one Hessian carrier in claim 12841.  `m` stands for
`M[A]` and the two coordinates are the displayed vector
`(-z/(2π), 1)`. -/
noncomputable def boundaryFreeHessian (m z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a : ℝ := -z / (2 * Real.pi)
  !![m * a * a, m * a;
     m * a,     m]

/-- The displayed Mellin image is an outer product and has zero determinant. -/
theorem boundaryFreeHessian_rankOne_det_zero (m z : ℝ) :
    let a : ℝ := -z / (2 * Real.pi)
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      !![m * a * a, m * a;
         m * a,     m]
    (∃ v w : Fin 2 → ℝ, ∀ i j, H i j = v i * w j) ∧
      Matrix.det H = 0 := by
  dsimp
  constructor
  · refine ⟨![m * (-z / (2 * Real.pi)), m], ![-z / (2 * Real.pi), 1], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.det_fin_two] <;> ring

end MathlibPlus.LinearAlgebra.Claim12841
