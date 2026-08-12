import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MathlibPlus.LinearAlgebra.Claim12953

open scoped Matrix

/-!
Formalization of admitted claim 12953.  The scalar matrix and the length-two
Jordan block are represented as the two upper-triangular 2-by-2 matrices over
`ℚ`.  The kernel equations and nilpotence orders are stated explicitly rather
than importing an unreviewed Jordan-form convention.
-/

def upperTriangular (t u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![t, u; 0, t]

lemma upperTriangular_charpoly (t u v : ℚ) :
    Matrix.charpoly (upperTriangular t u) =
      Matrix.charpoly (upperTriangular t v) := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  simp [upperTriangular, Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]

lemma upperTriangular_pow_shape (t u : ℚ) (n : ℕ) :
    ∃ b : ℚ, upperTriangular t u ^ n = !![t ^ n, b; 0, t ^ n] := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperTriangular]
  | succ n ih =>
      rcases ih with ⟨b, hb⟩
      refine ⟨t ^ n * u + b * t, ?_⟩
      rw [pow_succ, hb]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring_nf

lemma upperTriangular_trace_pow (t u : ℚ) (n : ℕ) :
    Matrix.trace (upperTriangular t u ^ n) = 2 * t ^ n := by
  rcases upperTriangular_pow_shape t u n with ⟨b, hb⟩
  rw [hb]
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num [two_mul]

lemma upperTriangular_kernel_scalar_zero :
    ∀ v : Fin 2 → ℚ, upperTriangular 0 0 *ᵥ v = 0 := by
  intro v
  funext i
  fin_cases i <;>
    simp [upperTriangular, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma upperTriangular_kernel_jordan_zero :
    ∀ v : Fin 2 → ℚ,
      upperTriangular 0 1 *ᵥ v = 0 ↔ v 1 = 0 := by
  intro v
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [upperTriangular, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    exact h0
  · intro h1
    funext i
    fin_cases i <;>
      simp [upperTriangular, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1]

/-- The explicit scalar/Jordan witness from claim 12953. -/
theorem claim12953 :
    (∀ t : ℚ,
      Matrix.charpoly (upperTriangular t 0) =
        Matrix.charpoly (upperTriangular t 1) ∧
      ∀ n : ℕ,
        Matrix.trace (upperTriangular t 0 ^ n) =
          Matrix.trace (upperTriangular t 1 ^ n)) ∧
    (∀ v : Fin 2 → ℚ, upperTriangular 0 0 *ᵥ v = 0) ∧
    (∀ v : Fin 2 → ℚ,
      upperTriangular 0 1 *ᵥ v = 0 ↔ v 1 = 0) ∧
    upperTriangular 0 0 = 0 ∧
    upperTriangular 0 1 ^ 2 = 0 ∧
    upperTriangular 0 1 ≠ 0 := by
  constructor
  · intro t
    constructor
    · exact upperTriangular_charpoly t 0 1
    · intro n
      rw [upperTriangular_trace_pow, upperTriangular_trace_pow]
  refine ⟨upperTriangular_kernel_scalar_zero, upperTriangular_kernel_jordan_zero, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [upperTriangular]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperTriangular, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h
    norm_num [upperTriangular] at h01

end MathlibPlus.LinearAlgebra.Claim12953
