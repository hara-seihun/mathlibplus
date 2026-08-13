import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim47537

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def U (a : ℝ) : Mat2 := !![1, a; 0, 1]
def Uinv (a : ℝ) : Mat2 := !![1, -a; 0, 1]
def L (b : ℝ) : Mat2 := !![1, 0; b, 1]
def Linv (b : ℝ) : Mat2 := !![1, 0; -b, 1]
def C (a b : ℝ) : Mat2 :=
  !![1 + a*b + a^2*b^2, -a^2*b; a*b^2, 1 - a*b]
def J : Mat2 := !![0, 1; -1, 0]
def cayleyM (a b : ℝ) : Mat2 :=
  (a^2*b^2 + 4)⁻¹ •
    !![2*a*b^2, -(2*a*b + a^2*b^2);
       -(2*a*b + a^2*b^2), 2*a^2*b]

theorem U_mul_Uinv (a : ℝ) : U a * Uinv a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, Uinv, Matrix.mul_apply]
  <;> ring

theorem Uinv_mul_U (a : ℝ) : Uinv a * U a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, Uinv, Matrix.mul_apply]
  <;> ring

theorem L_mul_Linv (b : ℝ) : L b * Linv b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L, Linv, Matrix.mul_apply]
  <;> ring

theorem Linv_mul_L (b : ℝ) : Linv b * L b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L, Linv, Matrix.mul_apply]
  <;> ring

theorem U_inv (a : ℝ) : (U a)⁻¹ = Uinv a := by
  exact Matrix.inv_eq_right_inv (U_mul_Uinv a)

theorem L_inv (b : ℝ) : (L b)⁻¹ = Linv b := by
  exact Matrix.inv_eq_right_inv (L_mul_Linv b)

theorem commutator_formula (a b : ℝ) :
    U a * L b * (U a)⁻¹ * (L b)⁻¹ = C a b := by
  rw [U_inv, L_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, Uinv, L, Linv, C, Matrix.mul_apply]
  <;> ring

theorem det_C_add_one (a b : ℝ) :
    Matrix.det (C a b + 1) = a^2*b^2 + 4 := by
  rw [Matrix.det_fin_two]
  simp [C, Matrix.add_apply, Matrix.one_apply]
  ring

theorem cayley_formula (a b : ℝ) :
    J * (C a b - 1) * (C a b + 1)⁻¹ = cayleyM a b := by
  have hd : a^2*b^2 + 4 ≠ 0 := by nlinarith [sq_nonneg (a*b)]
  have hdet : Matrix.det (C a b + 1) = a^2*b^2 + 4 := det_C_add_one a b
  have hCplus : C a b + 1 =
      !![2 + a*b + a^2*b^2, -a^2*b; a*b^2, 2 - a*b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, Matrix.add_apply, Matrix.one_apply]
    <;> ring
  have hN : J * (C a b - 1) =
      !![a*b^2, -a*b; -a*b - a^2*b^2, a^2*b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J, C, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    <;> ring
  rw [hN, Matrix.inv_def, hdet, hCplus, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C, cayleyM, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.smul_apply, hd]
  <;> field_simp
  <;> ring

/-- The explicit Cayley matrix is symmetric and has the negative determinant
that gives the claimed indefinite two-dimensional form. -/
theorem cayley_properties {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Matrix.det (C a b + 1) = a^2*b^2 + 4) ∧
      (cayleyM a b) 0 1 = (cayleyM a b) 1 0 ∧
      Matrix.det (cayleyM a b) = -a^2*b^2 / (a^2*b^2 + 4) ∧
      Matrix.det (cayleyM a b) < 0 := by
  have hd : a^2*b^2 + 4 ≠ 0 := by nlinarith [sq_nonneg (a*b)]
  have hdetM : Matrix.det (cayleyM a b) =
      -a^2*b^2 / (a^2*b^2 + 4) := by
    rw [Matrix.det_fin_two]
    simp [cayleyM, Matrix.smul_apply, hd]
    field_simp
    ring
  refine ⟨det_C_add_one a b, ?_, hdetM, ?_⟩
  · simp [cayleyM, Matrix.smul_apply]
  · have hab : 0 < a^2*b^2 := by positivity
    have hden : 0 < a^2*b^2 + 4 := by nlinarith [sq_nonneg (a*b)]
    rw [hdetM]
    have hneg : -a^2 * b^2 < 0 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
    exact div_neg_of_neg_of_pos hneg hden

end

end MathlibPlus.LinearAlgebra.Claim47537
