import Mathlib

namespace MathlibPlus.LinearAlgebra.PauliSquares

/--
Claim 4490, with the standard complex Pauli matrices made explicit.  The
second relation is the square of the scalar multiple `iY`.
-/
theorem pauliSquareRelations :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    X * X = 1 ∧
      (Complex.I • Y) * (Complex.I • Y) = -1 ∧
      Z * Z = 1 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
Claim 7007. The four displayed arithmetic coefficient matrices are a basis of
`M₂(ℂ)`, expressed by existence and uniqueness of their coordinates, and have
the stated multiplication table. The matrix called `J` is the source's `iY`.
-/
theorem pauliCoefficientBasisAndMultiplication_claim7007 :
    let I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let J : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ, ∃! c : Fin 4 → ℂ,
      A = c 0 • I₂ + c 1 • X + c 2 • J + c 3 • Z) ∧
      X * X = I₂ ∧ Z * Z = I₂ ∧ J * J = -I₂ ∧ Z * X = J ∧ X * Z = -J := by
  dsimp
  constructor
  · intro A
    let c : Fin 4 → ℂ :=
      ![(A 0 0 + A 1 1) / 2, (A 0 1 + A 1 0) / 2,
        (A 0 1 - A 1 0) / 2, (A 0 0 - A 1 1) / 2]
    refine ⟨c, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [c, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two] <;>
        ring
    · intro d hd
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hd
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hd
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hd
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hd
      simp [Matrix.add_apply, Matrix.smul_apply] at h00 h01 h10 h11
      funext i
      fin_cases i
      · dsimp [c]
        linear_combination -(1 / 2 : ℂ) * h00 - (1 / 2 : ℂ) * h11
      · dsimp [c]
        linear_combination -(1 / 2 : ℂ) * h01 - (1 / 2 : ℂ) * h10
      · dsimp [c]
        linear_combination -(1 / 2 : ℂ) * h01 + (1 / 2 : ℂ) * h10
      · dsimp [c]
        linear_combination -(1 / 2 : ℂ) * h00 + (1 / 2 : ℂ) * h11
  · constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.PauliSquares
