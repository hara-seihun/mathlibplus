import Mathlib

namespace MathlibPlus.LinearAlgebra.SemisimpleJordanCounterexample

open Polynomial

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℚ

/-- The scalar matrix from the semisimple/Jordan counterexample in claim 12323. -/
def semisimpleMatrix : Matrix2 := !![-3, 0; 0, -3]

/-- The nontrivial Jordan block from claim 12323. -/
def jordanMatrix : Matrix2 := !![-3, 1; 0, -3]

/-- The common characteristic polynomial asserted in claim 12323. -/
noncomputable def targetCharpoly : ℚ[X] := (X + C 3) ^ 2

/-- The shifted nilpotent part of the Jordan block. -/
def jordanShift : Matrix2 := jordanMatrix + (3 : ℚ) • (1 : Matrix2)

theorem semisimple_charpoly :
    Matrix.charpoly semisimpleMatrix = targetCharpoly := by
  simp [semisimpleMatrix, targetCharpoly, Matrix.charpoly_fin_two]
  ring

theorem jordan_charpoly :
    Matrix.charpoly jordanMatrix = targetCharpoly := by
  simp [jordanMatrix, targetCharpoly, Matrix.charpoly_fin_two]
  ring

private lemma jordan_00 : jordanMatrix 0 0 = (-3 : ℚ) := by rfl
private lemma jordan_01 : jordanMatrix 0 1 = (1 : ℚ) := by rfl
private lemma jordan_10 : jordanMatrix 1 0 = (0 : ℚ) := by rfl
private lemma jordan_11 : jordanMatrix 1 1 = (-3 : ℚ) := by rfl
private lemma semisimple_00 : semisimpleMatrix 0 0 = (-3 : ℚ) := by rfl
private lemma semisimple_11 : semisimpleMatrix 1 1 = (-3 : ℚ) := by rfl
private lemma semisimple_10 : semisimpleMatrix 1 0 = (0 : ℚ) := by rfl
private lemma semisimple_01 : semisimpleMatrix 0 1 = (0 : ℚ) := by rfl

private lemma jordan_power_entries (k : ℕ) :
    (jordanMatrix ^ k) 1 0 = 0 ∧
      (jordanMatrix ^ k) 0 0 = (-3 : ℚ) ^ k ∧
      (jordanMatrix ^ k) 1 1 = (-3 : ℚ) ^ k := by
  induction k with
  | zero =>
      norm_num [Matrix.one_apply]
  | succ k ih =>
      rcases ih with ⟨hlower, h00, h11⟩
      constructor
      · rw [pow_succ, Matrix.mul_apply]
        simp [Fin.sum_univ_two, jordan_00, jordan_01, jordan_10, jordan_11,
          hlower, h11]
      constructor
      · rw [pow_succ, Matrix.mul_apply]
        simp [Fin.sum_univ_two, jordan_00, jordan_01, jordan_10, jordan_11,
          h00]
        ring
      · rw [pow_succ, Matrix.mul_apply]
        simp [Fin.sum_univ_two, jordan_00, jordan_01, jordan_10, jordan_11,
          hlower, h11]
        ring

private lemma semisimple_power_entries (k : ℕ) :
    (semisimpleMatrix ^ k) 0 0 = (-3 : ℚ) ^ k ∧
      (semisimpleMatrix ^ k) 1 1 = (-3 : ℚ) ^ k := by
  induction k with
  | zero =>
      norm_num [Matrix.one_apply]
  | succ k ih =>
      rcases ih with ⟨h00, h11⟩
      constructor <;> rw [pow_succ, Matrix.mul_apply]
      · simp [Fin.sum_univ_two, semisimple_00, semisimple_10, h00]
        ring
      · simp [Fin.sum_univ_two, semisimple_00, semisimple_01, semisimple_10,
          semisimple_11, h11]
        ring

theorem semisimple_trace_pow (k : ℕ) :
    Matrix.trace (semisimpleMatrix ^ k) = 2 * (-3 : ℚ) ^ k := by
  rcases semisimple_power_entries k with ⟨h00, h11⟩
  simp [Matrix.trace, Fin.sum_univ_two, h00, h11]
  ring

theorem jordan_trace_pow (k : ℕ) :
    Matrix.trace (jordanMatrix ^ k) = 2 * (-3 : ℚ) ^ k := by
  rcases jordan_power_entries k with ⟨_, h00, h11⟩
  simp [Matrix.trace, Fin.sum_univ_two, h00, h11]
  ring

/-- The two matrices have identical scalar traces for every positive power,
indeed for every natural power, and the displayed common value is exact. -/
theorem equal_trace_powers (k : ℕ) :
    Matrix.trace (semisimpleMatrix ^ k) = Matrix.trace (jordanMatrix ^ k) ∧
      Matrix.trace (jordanMatrix ^ k) = 2 * (-3 : ℚ) ^ k := by
  exact ⟨(semisimple_trace_pow k).trans (jordan_trace_pow k).symm,
    jordan_trace_pow k⟩

theorem semisimple_shift_eq_zero :
    semisimpleMatrix + (3 : ℚ) • (1 : Matrix2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [semisimpleMatrix, Matrix.smul_apply, Matrix.one_apply]

theorem jordan_shift_eq_explicit : jordanShift = !![0, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanShift, jordanMatrix, Matrix.smul_apply, Matrix.one_apply,
      Matrix.add_apply]

theorem jordan_shift_ne_zero : jordanShift ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [jordanShift, jordanMatrix, Matrix.smul_apply, Matrix.one_apply,
    Matrix.add_apply] at h01

theorem jordan_shift_sq_eq_zero : jordanShift ^ 2 = 0 := by
  rw [jordan_shift_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private lemma semisimple_scalar :
    semisimpleMatrix = (-3 : ℚ) • (1 : Matrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [semisimpleMatrix, Matrix.smul_apply, Matrix.one_apply]

/-- The two matrices are not similar over `ℚ`; a scalar matrix cannot be
conjugate to the nontrivial Jordan block. -/
theorem not_similar :
    ¬ ∃ P : Matrix2ˣ,
      (P : Matrix2) * semisimpleMatrix * (↑(P⁻¹) : Matrix2) = jordanMatrix := by
  rintro ⟨P, hP⟩
  rw [semisimple_scalar] at hP
  have hscalar :
      (P : Matrix2) * ((-3 : ℚ) • (1 : Matrix2)) * (↑(P⁻¹) : Matrix2) =
        (-3 : ℚ) • (1 : Matrix2) := by
    simp [Matrix.mul_smul]
  rw [hscalar] at hP
  have h01 := congr_fun (congr_fun hP 0) 1
  norm_num [jordanMatrix, Matrix.smul_apply, Matrix.one_apply] at h01

end MathlibPlus.LinearAlgebra.SemisimpleJordanCounterexample
