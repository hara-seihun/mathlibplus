import MathlibPlus.LinearAlgebra.DegreeOneMatrixModel

namespace MathlibPlus.LinearAlgebra.Claim14800

open MathlibPlus.LinearAlgebra.DegreeOneMatrixModel

/-- The explicit complex `2 × 2` matrix model of the commuting Klingen
involutions and the two eigenspace descriptions in admitted claim 14800.
The source's `span` notation is represented by the equivalent two-generator
linear-combination characterization. -/
theorem klingenInvolutions_and_eigenspaces :
    let Y : Mat2 := !![0, -Complex.I; Complex.I, 0]
    let Z : Mat2 := !![1, 0; 0, -1]
    (∀ B : Mat2, R_h (R_h B) = B) ∧
      (∀ B : Mat2, R_c (R_c B) = B) ∧
      (∀ B : Mat2, R_h (R_c B) = R_c (R_h B)) ∧
      (∀ B : Mat2, D B = X * B * X) ∧
      (∀ B : Mat2, D B = B ↔
        ∃ a b : ℂ, B = a • (1 : Mat2) + b • X) ∧
      (∀ B : Mat2, D B = -B ↔
        ∃ a b : ℂ, B = a • Z + b • ((Complex.I : ℂ) • Y)) := by
  dsimp [R_h, R_c, D, X]
  let X0 : Mat2 := !![0, 1; 1, 0]
  let Y0 : Mat2 := !![0, -Complex.I; Complex.I, 0]
  let Z0 : Mat2 := !![1, 0; 0, -1]
  have hX : X0 * X0 = (1 : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X0, Matrix.mul_apply, Fin.sum_univ_two]
  have hleft (B : Mat2) : X0 * (X0 * B) = B := by
    rw [← Matrix.mul_assoc, hX, one_mul]
  have hright (B : Mat2) : (B * X0) * X0 = B := by
    rw [Matrix.mul_assoc, hX, mul_one]
  have hcomm (B : Mat2) : X0 * (B * X0) = (X0 * B) * X0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc]
  refine ⟨hleft, hright, hcomm, ?_, ?_, ?_⟩
  · intro B
    rfl
  · intro B
    constructor
    · intro hB
      have h01 := congrArg (fun M : Mat2 => M 0 1) hB
      have h11 := congrArg (fun M : Mat2 => M 1 1) hB
      simp [X0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two] at h01 h11
      refine ⟨B 0 0, B 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Matrix.smul_apply, Fin.sum_univ_two] <;>
        try { exact h01 } <;>
        try { exact h01.symm } <;>
        try { exact h11 } <;>
        try { exact h11.symm }
    · rintro ⟨a, b, rfl⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Matrix.smul_apply, Fin.sum_univ_two]
  · intro B
    constructor
    · intro hB
      have h10 := congrArg (fun M : Mat2 => M 1 0) hB
      have h11 := congrArg (fun M : Mat2 => M 1 1) hB
      simp [X0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two] at h10 h11
      have h10' : B 1 0 = -B 0 1 := by
        calc
          B 1 0 = -(-B 1 0) := by ring
          _ = -B 0 1 := by rw [← h10]
      have h11' : B 1 1 = -B 0 0 := by
        calc
          B 1 1 = -(-B 1 1) := by ring
          _ = -B 0 0 := by rw [← h11]
      refine ⟨B 0 0, B 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X0, Y0, Z0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Matrix.smul_apply, Fin.sum_univ_two] <;>
        try { exact h10' } <;>
        try { exact h11' } <;>
        try { exact h10'.symm } <;>
        try { exact h11'.symm }
    · rintro ⟨a, b, rfl⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X0, Y0, Z0, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Matrix.smul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.Claim14800
