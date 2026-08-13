import Mathlib

namespace MathlibPlus.Analysis.Claim2180

/-- The three explicit crossing-sign cases from claim 2180, retaining the
source boundary-ratio and eigenvalue functions as interfaces and preserving
their displayed values. -/
theorem allThreeCrossingSigns_claim2180
    (boundary O lambda : ℝ → ℝ)
    (h2_boundary : boundary 2 = Real.sqrt 2 - 1)
    (h2_gap : O 2 - lambda 2 = 1)
    (hinv_boundary : boundary (1 / Real.sqrt 2) = 0)
    (hinv_O : O (1 / Real.sqrt 2) = -1 / Real.sqrt 2)
    (hinv_lambda : lambda (1 / Real.sqrt 2) = -1 / Real.sqrt 2)
    (h0_boundary : boundary 0 = 1 - Real.sqrt 2)
    (h0_O : O 0 = -Real.sqrt 2)
    (h0_lambda : lambda 0 = -1) :
    (0 < boundary 2 ∧ 0 < O 2 - lambda 2) ∧
      (boundary (1 / Real.sqrt 2) = 0 ∧
        O (1 / Real.sqrt 2) = lambda (1 / Real.sqrt 2) ∧
        O (1 / Real.sqrt 2) = -1 / Real.sqrt 2) ∧
      (boundary 0 < 0 ∧ O 0 < lambda 0) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [h2_boundary, h2_gap]
    exact ⟨by linarith, by norm_num⟩
  · refine ⟨hinv_boundary, ?_, hinv_O⟩
    rw [hinv_O, hinv_lambda]
  · rw [h0_boundary, h0_O, h0_lambda]
    exact ⟨by linarith, by linarith⟩

end MathlibPlus.Analysis.Claim2180
