import Mathlib

namespace MathlibPlus.Analysis.Claim17393

/-- The defect profile `(2b - 1) cosh (u / 2)` is annihilated by
`D² - 1/4`. -/
theorem defectAnnihilated_claim17393 (b : ℝ) :
    ∀ u : ℝ,
      deriv (deriv (fun v : ℝ => (2 * b - 1) * Real.cosh (v / 2))) u -
          (1 / 4 : ℝ) * ((2 * b - 1) * Real.cosh (u / 2)) = 0 := by
  intro u
  let f : ℝ → ℝ := fun v => (2 * b - 1) * Real.cosh (v / 2)
  let g : ℝ → ℝ := fun v => (2 * b - 1) * (1 / 2 : ℝ) * Real.sinh (v / 2)
  have hf : ∀ v : ℝ, HasDerivAt f (g v) v := by
    intro v
    dsimp [f, g]
    simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((Real.hasDerivAt_cosh (v / 2)).comp v
        ((hasDerivAt_id v).div_const 2)).const_mul (2 * b - 1)
  have hderivf : deriv f = g := by
    funext v
    exact (hf v).deriv
  have hg : ∀ v : ℝ,
      HasDerivAt g ((2 * b - 1) * (1 / 2 : ℝ) * (1 / 2 : ℝ) * Real.cosh (v / 2)) v := by
    intro v
    dsimp [g]
    simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((Real.hasDerivAt_sinh (v / 2)).comp v
        ((hasDerivAt_id v).div_const 2)).const_mul ((2 * b - 1) * (1 / 2 : ℝ))
  change deriv (deriv f) u - (1 / 4 : ℝ) * f u = 0
  rw [hderivf, (hg u).deriv]
  dsimp [f, g]
  ring

end MathlibPlus.Analysis.Claim17393
