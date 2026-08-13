import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim13658

/--
The two eigenspaces of conjugation by the Pauli matrix `X` are written in
coordinate form.  The existential two-coefficient descriptions are exactly
the spans of `{I, X}` and `{Z, iY}` respectively; the explicit matrix
calculation also records that left and right multiplication by `X` agree on
the `+1` eigenspace.
-/
theorem pairedAndSingleFlipEigenspaces_claim13658 :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let iY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
    ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      (X * M * X = M ↔
        ∃ a b : ℂ, M = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • X) ∧
      (X * M * X = -M ↔
        ∃ a b : ℂ, M = a • Z + b • iY) ∧
      (X * M * X = M → X * M = M * X) := by
  dsimp
  intro M
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let iY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
  have hswap : X * M * X =
      !![M 1 1, M 1 0; M 0 1, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two]
  constructor
  · constructor
    · intro h
      rw [hswap] at h
      refine ⟨M 0 0, M 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
      · simpa using (congrFun (congrFun h 1) 0).symm
      · simpa using (congrFun (congrFun h 1) 1).symm
    · rintro ⟨a, b, rfl⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two]
  · constructor
    · constructor
      · intro h
        rw [hswap] at h
        refine ⟨M 0 0, M 0 1, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Z, iY]
        · simp [Z, iY]
        · simpa using congrFun (congrFun h 0) 1
        · simpa using congrFun (congrFun h 0) 0
      · rintro ⟨a, b, rfl⟩
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [X, Z, iY, Matrix.mul_apply, Matrix.vecMul, dotProduct,
            Fin.sum_univ_two]
    · intro h
      rw [hswap] at h
      have h10 := congrFun (congrFun h 1) 0
      have h11 := congrFun (congrFun h 1) 1
      simp at h10 h11
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, h10, h11]

end MathlibPlus.LinearAlgebra.Claim13658
