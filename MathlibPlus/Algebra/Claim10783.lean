import Mathlib

namespace MathlibPlus.Algebra.Claim10783

open Matrix

/-- The explicit reciprocal quadratic witness from admitted claim 10783.

The normalized roots preserve the split trace form under diagonal dilation, but
not the positive identity form. -/
theorem reciprocalRootSplitFormWitness_claim10783 :
    let a : ℝ := (-7 + Real.sqrt 13) / 6
    let b : ℝ := (-7 - Real.sqrt 13) / 6
    let split : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let dilation : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]
    let identity : Matrix (Fin 2) (Fin 2) ℝ := 1
    a * b = 1 ∧
      a + b = -(7 / 3 : ℝ) ∧
      dilation.transpose * split * dilation = split ∧
      dilation.transpose * identity * dilation ≠ identity ∧
      |a| ≠ 1 ∧
      |b| ≠ 1 ∧
      |a + b| = 7 / 3 ∧
      2 < (7 / 3 : ℝ) := by
  dsimp only
  have hsqrt_sq : (Real.sqrt 13) ^ 2 = (13 : ℝ) := by norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg _
  have hsqrt_lt_seven : Real.sqrt 13 < 7 := by
    nlinarith
  have ha_neg : (-7 + Real.sqrt 13) / 6 < (0 : ℝ) := by
    nlinarith
  have hb_neg : (-7 - Real.sqrt 13) / 6 < (0 : ℝ) := by
    nlinarith
  have hab : ((-7 + Real.sqrt 13) / 6) * ((-7 - Real.sqrt 13) / 6) = (1 : ℝ) := by
    nlinarith
  have habsum : ((-7 + Real.sqrt 13) / 6) + ((-7 - Real.sqrt 13) / 6) = -(7 / 3 : ℝ) := by
    ring
  refine ⟨hab, habsum, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [hsqrt_sq]
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    have hsq : ((-7 + Real.sqrt 13) / 6) ^ 2 ≠ (1 : ℝ) := by
      intro hs
      nlinarith [hsqrt_sq]
    apply hsq
    have hprod : ((-7 + Real.sqrt 13) / 6) * ((-7 + Real.sqrt 13) / 6) = (1 : ℝ) := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    simpa only [pow_two] using hprod
  · rw [abs_of_neg ha_neg]
    intro h
    nlinarith
  · rw [abs_of_neg hb_neg]
    intro h
    nlinarith
  · rw [habsum]
    norm_num [abs_of_nonpos]

end MathlibPlus.Algebra.Claim10783
