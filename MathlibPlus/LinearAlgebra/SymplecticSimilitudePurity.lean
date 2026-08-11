import Mathlib

namespace MathlibPlus.LinearAlgebra

noncomputable section

/--
Formalization of admitted claim 11047.  The two decimal root moduli in the
source are represented by the exact roots of the displayed polynomial; the
last conjunct records the claimed failure of modulus `3`.
-/
theorem symplecticSimilitudePurityBlind :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -9; 1, -7]
    let p : Polynomial ℝ :=
      Matrix.det ((Polynomial.X : Polynomial ℝ) •
        (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℝ)) -
        A.map Polynomial.C)
    A.transpose * J * A = 9 • J ∧
      p = Polynomial.X ^ 2 + 7 * Polynomial.X + 9 ∧
      (∀ x : ℝ, p.eval x = 0 ↔
        x = (-7 + Real.sqrt 13) / 2 ∨ x = (-7 - Real.sqrt 13) / 2) ∧
      (∀ x : ℝ, p.eval x = 0 → |x| ≠ 3) := by
  dsimp
  have hsim :
      (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ).transpose *
          !![0, 1; -1, 0] * !![0, -9; 1, -7] =
        9 • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hpoly :
      Matrix.det ((Polynomial.X : Polynomial ℝ) •
          (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℝ)) -
          (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ).map Polynomial.C) =
        Polynomial.X ^ 2 + 7 * Polynomial.X + 9 := by
    rw [Matrix.det_fin_two]
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    change
      Polynomial.X * (Polynomial.X + Polynomial.C 7) + Polynomial.C 9 =
        Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X + Polynomial.C 9
    ring
  refine ⟨hsim, hpoly, ?_, ?_⟩
  · rw [hpoly]
    intro x
    have hs : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := by
      have : (0 : ℝ) ≤ 13 := by norm_num
      simpa using (Real.sq_sqrt this)
    constructor
    · intro hx
      have hquad : x ^ 2 + 7 * x + 9 = 0 := by
        simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow] using hx
      have hfac :
          (2 * x + 7 - Real.sqrt 13) * (2 * x + 7 + Real.sqrt 13) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfac with hplus | hminus
      · left
        nlinarith
      · right
        nlinarith
    · rintro (rfl | rfl)
      · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
        nlinarith
      · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
        nlinarith
  · rw [hpoly]
    intro x hx hthree
    have hquad : x ^ 2 + 7 * x + 9 = 0 := by
      simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow] using hx
    have habs : x = 3 ∨ x = -3 := by
      rcases le_total 0 x with hx0 | hxneg
      · left
        rw [abs_of_nonneg hx0] at hthree
        linarith
      · right
        rw [abs_of_nonpos hxneg] at hthree
        linarith
    rcases habs with rfl | rfl <;> norm_num at hquad

end
end MathlibPlus.LinearAlgebra
