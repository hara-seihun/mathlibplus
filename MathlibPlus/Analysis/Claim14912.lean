import Mathlib

namespace MathlibPlus.Analysis.Claim14912

/-- The reciprocal-gap derivative of the normalized lowest-eigenvector
coordinate from the source's two-by-two family. -/
theorem reciprocalGapDerivative (ε : ℝ) (hε : 0 < ε) :
    deriv (fun t : ℝ => -2 * t / (ε + Real.sqrt (ε ^ 2 + 4 * t ^ 2))) 0 = -1 / ε := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hinner : HasDerivAt (fun t : ℝ => ε ^ 2 + 4 * t ^ 2) 0 0 := by
    have hquad : HasDerivAt (fun t : ℝ => 4 * t ^ 2) 0 0 := by
      simpa [Pi.pow_apply, id_eq] using
        (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 4)
    exact hquad.const_add (ε ^ 2)
  have harg0 : ε ^ 2 + 4 * (0 : ℝ) ^ 2 ≠ 0 := by
    rw [show ε ^ 2 + 4 * (0 : ℝ) ^ 2 = ε ^ 2 by ring]
    exact pow_ne_zero 2 hε0
  have hsqrt : HasDerivAt
      (fun t : ℝ => Real.sqrt (ε ^ 2 + 4 * t ^ 2))
      (0 / (2 * Real.sqrt (ε ^ 2))) 0 := by
    have h := HasDerivAt.comp 0 (Real.hasDerivAt_sqrt harg0) hinner
    simpa [Function.comp_def, show ε ^ 2 + 4 * (0 : ℝ) ^ 2 = ε ^ 2 by ring] using h
  have hden : HasDerivAt
      (fun t : ℝ => ε + Real.sqrt (ε ^ 2 + 4 * t ^ 2))
      (0 / (2 * Real.sqrt (ε ^ 2))) 0 := by
    exact hsqrt.const_add ε
  have hden0 : ε + Real.sqrt (ε ^ 2 + 4 * (0 : ℝ) ^ 2) ≠ 0 := by
    rw [show ε ^ 2 + 4 * (0 : ℝ) ^ 2 = ε ^ 2 by ring,
      Real.sqrt_sq (le_of_lt hε)]
    linarith
  have hnum : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-2 : ℝ))
  have hquot := hnum.div hden hden0
  have hfun :
      (fun t : ℝ => -2 * t) / (fun t => ε + Real.sqrt (ε ^ 2 + 4 * t ^ 2)) =
        (fun t : ℝ => -2 * t / (ε + Real.sqrt (ε ^ 2 + 4 * t ^ 2))) := by
    funext t
    rfl
  rw [hfun] at hquot
  have hderiv : -(2 * (ε + ε)) / (ε + ε) ^ 2 = -1 / ε := by
    field_simp [hε0]
    ring
  simpa [show ε ^ 2 + 4 * (0 : ℝ) ^ 2 = ε ^ 2 by ring,
    Real.sqrt_sq (le_of_lt hε), hderiv] using hquot.deriv

end MathlibPlus.Analysis.Claim14912
