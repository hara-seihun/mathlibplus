import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7761

/-- The finite negative determinant witness in claim 7761, retaining the
source's physical parameter interface. -/
theorem finiteOneDyadicCounterexample (theta U Phi : ℝ)
    (hx : Real.cos theta ^ 2 = (2 : ℝ) / 5)
    (hU : Real.cosh U = 2)
    (hPhi : Phi = Real.pi / 2) :
    let lam : ℝ := 1 / Real.sqrt 2
    let A : ℝ := (2 + Real.cos theta ^ 2) * Real.cosh U - 2 * Real.cos Phi
    let C : ℝ :=
      3 * Real.sqrt 2 * Real.sin (2 * theta) * Real.sinh U * Real.sin Phi
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![A, lam * C; lam * C, A]
    A = 24 / 5 ∧ C ^ 2 = 1296 / 25 ∧
      Matrix.det M = -72 / 25 ∧ Matrix.det M < 0 := by
  dsimp only
  let A : ℝ := (2 + Real.cos theta ^ 2) * Real.cosh U - 2 * Real.cos Phi
  let C : ℝ :=
    3 * Real.sqrt 2 * Real.sin (2 * theta) * Real.sinh U * Real.sin Phi
  change A = 24 / 5 ∧ C ^ 2 = 1296 / 25 ∧
    Matrix.det (!![A, (1 / Real.sqrt 2) * C;
      (1 / Real.sqrt 2) * C, A] : Matrix (Fin 2) (Fin 2) ℝ) = -72 / 25 ∧
      Matrix.det (!![A, (1 / Real.sqrt 2) * C;
        (1 / Real.sqrt 2) * C, A] : Matrix (Fin 2) (Fin 2) ℝ) < 0
  have htrig : Real.sin theta ^ 2 + Real.cos theta ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq theta
  have hsin2 : Real.sin (2 * theta) ^ 2 = (24 : ℝ) / 25 := by
    rw [Real.sin_two_mul]
    nlinarith [htrig, hx]
  have hhyper : Real.cosh U ^ 2 - Real.sinh U ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq U
  have hsinh : Real.sinh U ^ 2 = 3 := by
    nlinarith [hhyper, hU]
  have hsqrt : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlam : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
    field_simp [ne_of_gt hsqrtpos]
    nlinarith [hsqrt]
  have hA : A = (24 : ℝ) / 5 := by
    dsimp [A]
    rw [hPhi, Real.cos_pi_div_two]
    nlinarith [hx, hU]
  have hC : C ^ 2 = (1296 : ℝ) / 25 := by
    dsimp [C]
    rw [hPhi, Real.sin_pi_div_two]
    calc
      (3 * Real.sqrt 2 * Real.sin (2 * theta) * Real.sinh U * 1) ^ 2 =
          9 * (Real.sqrt 2) ^ 2 * Real.sin (2 * theta) ^ 2 *
            Real.sinh U ^ 2 := by ring
      _ = (1296 : ℝ) / 25 := by
        rw [hsqrt, hsin2, hsinh]
        norm_num
  have hdet :
      Matrix.det
          (!![A, (1 / Real.sqrt 2) * C;
              (1 / Real.sqrt 2) * C, A] : Matrix (Fin 2) (Fin 2) ℝ) =
        -(72 : ℝ) / 25 := by
    rw [Matrix.det_fin_two]
    change A * A - ((1 / Real.sqrt 2) * C) * ((1 / Real.sqrt 2) * C) =
      -(72 : ℝ) / 25
    calc
      A * A - ((1 / Real.sqrt 2) * C) * ((1 / Real.sqrt 2) * C) =
          A ^ 2 - (1 / Real.sqrt 2) ^ 2 * C ^ 2 := by ring
      _ = -(72 : ℝ) / 25 := by
        rw [hA, hC, hlam]
        norm_num
  exact ⟨hA, hC, hdet, by rw [hdet]; norm_num⟩

end MathlibPlus.LinearAlgebra.Claim7761
