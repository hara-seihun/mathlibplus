-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace MathlibPlus.Algebra.Claim7082

open Matrix
open Polynomial

theorem repeatedHallRelation_claim7082 :
    let Frel : Matrix (Fin 2) (Fin 2) ℤ := !![(-3 : ℤ), 1; 0, -3]
    let F9 : Matrix (Fin 2) (Fin 2) ℤ := !![(-3 : ℤ), 0; 0, -3]
    Matrix.charpoly Frel = Matrix.charpoly F9 ∧
      (∀ n : ℕ, 0 < n → Matrix.trace (Frel ^ n) = Matrix.trace (F9 ^ n)) ∧
      Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 ∧
      (Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2 = 0 ∧
      ¬ ∃ P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
        (P : Matrix (Fin 2) (Fin 2) ℤ) * F9 *
            (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = Frel := by
  let Frel : Matrix (Fin 2) (Fin 2) ℤ := !![(-3 : ℤ), 1; 0, -3]
  let F9 : Matrix (Fin 2) (Fin 2) ℤ := !![(-3 : ℤ), 0; 0, -3]
  change Matrix.charpoly Frel = Matrix.charpoly F9 ∧
      (∀ n : ℕ, 0 < n → Matrix.trace (Frel ^ n) = Matrix.trace (F9 ^ n)) ∧
      Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 ∧
      (Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2 = 0 ∧
      ¬ ∃ P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
        (P : Matrix (Fin 2) (Fin 2) ℤ) * F9 *
            (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = Frel
  have hchar : Matrix.charpoly Frel = Matrix.charpoly F9 := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two, Frel, F9,
      Matrix.scalar_apply]
  have hF9 : F9 = (-3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    native_decide
  have hlower (n : ℕ) : (Frel ^ n) (1 : Fin 2) 0 = 0 := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        rw [ih]
        norm_num [Frel]
  have hrel00 (n : ℕ) : (Frel ^ n) (0 : Fin 2) 0 = (-3 : ℤ) ^ n := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        rw [ih]
        norm_num [Frel]
        ring
  have hrel11 (n : ℕ) : (Frel ^ n) (1 : Fin 2) 1 = (-3 : ℤ) ^ n := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        rw [hlower, ih]
        norm_num [Frel]
        ring
  have hscalar00 (n : ℕ) : (F9 ^ n) (0 : Fin 2) 0 = (-3 : ℤ) ^ n := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        rw [ih]
        norm_num [F9]
        ring
  have hscalar11 (n : ℕ) : (F9 ^ n) (1 : Fin 2) 1 = (-3 : ℤ) ^ n := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        rw [ih]
        norm_num [F9]
        ring
  have htrace : ∀ n : ℕ, 0 < n → Matrix.trace (Frel ^ n) = Matrix.trace (F9 ^ n) := by
    intro n _
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two,
      hrel00, hrel11, hscalar00, hscalar11]
  have hne : Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 := by
    native_decide
  have hnil : (Frel + (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2 = 0 := by
    native_decide
  have hconj : ¬ ∃ P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
      (P : Matrix (Fin 2) (Fin 2) ℤ) * F9 *
          (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = Frel := by
    rintro ⟨P, hP⟩
    have hs : (P : Matrix (Fin 2) (Fin 2) ℤ) * F9 *
        (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = F9 := by
      rw [hF9]
      rw [Matrix.mul_smul, Matrix.smul_mul]
      simp
    rw [hs] at hP
    have h01 := congr_fun (congr_fun hP (0 : Fin 2)) (1 : Fin 2)
    norm_num [Frel, F9] at h01
  exact ⟨hchar, htrace, hne, hnil, hconj⟩

end MathlibPlus.Algebra.Claim7082
