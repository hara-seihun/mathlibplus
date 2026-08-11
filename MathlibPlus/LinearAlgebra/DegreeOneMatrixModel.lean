import Mathlib

namespace MathlibPlus.LinearAlgebra.DegreeOneMatrixModel

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The matrix `X` in the degree-one model. -/
def X : Mat2 := !![0, 1; 1, 0]

/-- The transpose map `S₁`. -/
def S_one (M : Mat2) : Mat2 := M.transpose

/-- Left multiplication by `X`. -/
def R_h (M : Mat2) : Mat2 := X * M

/-- Right multiplication by `X`. -/
def R_c (M : Mat2) : Mat2 := M * X

/-- The conjugation map displayed in the packet. -/
def D (M : Mat2) : Mat2 := X * M * X

/-- The square of transpose after left multiplication by `X`. -/
def transposeCompLX (M : Mat2) : Mat2 := (X * M).transpose

/-- Conjugation by the involution `X`. -/
def Ad_X (M : Mat2) : Mat2 := X * M * X

/-- The matrix-side identities in the degree-one model. -/
theorem degreeOneMatrixModel (M : Mat2) :
    S_one M = M.transpose ∧
      R_h M = X * M ∧
      R_c M = M * X ∧
      D M = X * M * X := by
  simp [S_one, R_h, R_c, D]

/-- Since `X` is symmetric and involutive, the square of `transpose ∘ L_X`
is conjugation by `X`. -/
theorem transposeCompLX_sq_eq_Ad_X (M : Mat2) :
    transposeCompLX (transposeCompLX M) = Ad_X M := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transposeCompLX, Ad_X, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, X]


/--
Claim 11716.  The two displayed 2-by-2 families have equal characteristic
polynomials and equal traces of every natural power, while their zero-scalar
members have different kernels and different nilpotence indices.
-/
theorem scalarSpectralData_not_JordanMultiplicity (t : ℝ) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![t, 0; 0, t]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![t, 1; 0, t]
    D.charpoly = J.charpoly ∧
      (∀ k : ℕ, Matrix.trace (D ^ k) = Matrix.trace (J ^ k)) ∧
      ({v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0} ≠
        {v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0}) ∧
      (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by
  let D : Matrix (Fin 2) (Fin 2) ℝ := !![t, 0; 0, t]
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![t, 1; 0, t]
  change D.charpoly = J.charpoly ∧
      (∀ k : ℕ, Matrix.trace (D ^ k) = Matrix.trace (J ^ k)) ∧
      ({v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0} ≠
        {v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0}) ∧
      (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0
  have hchar : D.charpoly = J.charpoly := by
    rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
    dsimp [D, J]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  have hD : ∀ k : ℕ, D ^ k = !![t ^ k, 0; 0, t ^ k] := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [D, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
  have hJ : ∀ k : ℕ, ∃ u : ℝ, J ^ k = !![t ^ k, u; 0, t ^ k] := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, ?_⟩
        simp only [pow_zero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        obtain ⟨u, hu⟩ := ih
        refine ⟨u * t + t ^ k, ?_⟩
        rw [pow_succ, hu]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [J, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
        ring
  have htrace : ∀ k : ℕ, Matrix.trace (D ^ k) = Matrix.trace (J ^ k) := by
    intro k
    rw [hD k]
    obtain ⟨u, hu⟩ := hJ k
    rw [hu]
    simp [Matrix.trace_fin_two]
  have hker :
      ({v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0} ≠
        {v : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0}) := by
    intro heq
    let v : Fin 2 → ℝ := ![0, 1]
    have hv0 :
        Matrix.mulVec (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0 := by
      ext i
      fin_cases i <;> simp [v, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
    have hv1 :
        Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      norm_num [v, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two] at h0
    have hv1' :
        Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = 0 := by
      have hmem : v ∈ {w : Fin 2 → ℝ |
          Matrix.mulVec (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) w = 0} := by
        rw [← heq]
        exact hv0
      exact hmem
    exact hv1 hv1'
  refine ⟨hchar, htrace, hker, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.DegreeOneMatrixModel
