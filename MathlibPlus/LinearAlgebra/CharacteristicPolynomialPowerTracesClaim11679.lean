import Mathlib

namespace MathlibPlus.LinearAlgebra

noncomputable section

abbrev claim11679TwoVec := Fin 2 → ℝ

def claim11679ZeroTwo : Matrix (Fin 2) (Fin 2) ℝ := 0

def claim11679JordanTwo : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

def claim11679KernelDimension (A : Matrix (Fin 2) (Fin 2) ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin A))

private def e0 : claim11679TwoVec := Pi.single (0 : Fin 2) 1

lemma claim11679JordanTwo_sq : claim11679JordanTwo ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [claim11679JordanTwo, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma claim11679JordanTwo_ne_zero : claim11679JordanTwo ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [claim11679JordanTwo] at h01

lemma claim11679JordanTwo_kernel :
    LinearMap.ker (Matrix.mulVecLin claim11679JordanTwo) = ℝ ∙ e0 := by
  ext x
  constructor
  · intro hx
    have hx0 : claim11679JordanTwo.mulVec x 0 = 0 := by
      have h := (LinearMap.mem_ker.mp hx)
      exact congrFun h 0
    have hx1 : x 1 = 0 := by
      simpa [claim11679JordanTwo, Matrix.mulVec, Fin.sum_univ_two,
        Matrix.vecHead, Matrix.vecTail] using hx0
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i
    · simp [e0]
    · simp [e0, hx1]
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;> simp [Matrix.mulVecLin_apply, claim11679JordanTwo, e0,
      Matrix.mulVec, Fin.sum_univ_two]

lemma claim11679ZeroTwo_kernel :
    LinearMap.ker (Matrix.mulVecLin claim11679ZeroTwo) = (⊤ : Submodule ℝ claim11679TwoVec) := by
  rw [LinearMap.ker_eq_top]
  apply LinearMap.ext
  intro x
  simp [claim11679ZeroTwo, Matrix.mulVecLin_apply]

/-- Claim 11679: the zero matrix and the nonzero length-two nilpotent Jordan
block have identical characteristic polynomials and all positive power traces,
but different kernel dimensions. -/
theorem characteristicPolynomialPowerTraces_claim11679 :
    Matrix.charpoly claim11679ZeroTwo = Polynomial.X ^ 2 ∧
      Matrix.charpoly claim11679JordanTwo = Polynomial.X ^ 2 ∧
      (∀ n : ℕ, 0 < n →
        Matrix.trace (claim11679ZeroTwo ^ n) = 0 ∧
          Matrix.trace (claim11679JordanTwo ^ n) = 0) ∧
      claim11679KernelDimension claim11679ZeroTwo = 2 ∧
      claim11679KernelDimension claim11679JordanTwo = 1 ∧
      claim11679JordanTwo ≠ 0 ∧ claim11679JordanTwo ^ 2 = 0 := by
  have hzchar : Matrix.charpoly claim11679ZeroTwo = Polynomial.X ^ 2 := by
    simpa [claim11679ZeroTwo] using
      (Matrix.charpoly_zero (R := ℝ) (n := Fin 2))
  have hjchar : Matrix.charpoly claim11679JordanTwo = Polynomial.X ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    norm_num [claim11679JordanTwo, Matrix.trace, Matrix.det_fin_two]
  have htraces : ∀ n : ℕ, 0 < n →
      Matrix.trace (claim11679ZeroTwo ^ n) = 0 ∧ Matrix.trace (claim11679JordanTwo ^ n) = 0 := by
    intro n hn
    constructor
    · rw [show claim11679ZeroTwo ^ n = 0 by
        exact zero_pow (Nat.ne_of_gt hn)]
      exact Matrix.trace_zero (Fin 2) ℝ
    · by_cases hn1 : n = 1
      · subst n
        norm_num [claim11679JordanTwo, Matrix.trace]
      · have hn2 : 2 ≤ n := by omega
        rw [show claim11679JordanTwo ^ n = 0 by
            exact pow_eq_zero_of_le hn2 claim11679JordanTwo_sq]
        exact Matrix.trace_zero (Fin 2) ℝ
  have hzeroDim : claim11679KernelDimension claim11679ZeroTwo = 2 := by
    rw [claim11679KernelDimension, claim11679ZeroTwo_kernel]
    simpa using (Module.finrank_fin_fun ℝ (n := 2))
  have hjDim : claim11679KernelDimension claim11679JordanTwo = 1 := by
    rw [claim11679KernelDimension, claim11679JordanTwo_kernel]
    exact finrank_span_singleton (by
      intro h
      have h0 := congrFun h 0
      simp [e0] at h0)
  exact ⟨hzchar, hjchar, htraces, hzeroDim, hjDim,
    claim11679JordanTwo_ne_zero, claim11679JordanTwo_sq⟩

end

end MathlibPlus.LinearAlgebra
