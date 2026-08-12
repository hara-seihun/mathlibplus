import Mathlib

/-!
# Scale-three Gevrey cutoff

The admitted claim specifies the formula on the open interval
`1/2 < t < 1` and the left/right extension of `χ₃`.  The interval argument
of `rho3` is therefore a subtype, while `chi3` is defined on all real inputs.
-/

namespace MathlibPlus.Analysis.Claim3081

/-- The scale-three ratio `ρ₃` on the interval specified in claim 3081. -/
noncomputable def rho3 (t : {t : ℝ // (1 / 2 : ℝ) < t ∧ t < 1}) : ℝ :=
  let a : ℝ := Real.exp (-((t.1 - (1 / 2 : ℝ))⁻¹ ^ 4))
  let b : ℝ := Real.exp (-3 * ((1 - t.1)⁻¹ ^ 4))
  a / (a + b)

/-- The cutoff `χ₃`, extended by one on the left and zero on the right. -/
noncomputable def chi3 (t : ℝ) : ℝ :=
  if t ≤ (1 / 2 : ℝ) then 1
  else if t < 1 then
    1 -
      (Real.exp (-((t - (1 / 2 : ℝ))⁻¹ ^ 4)) /
        (Real.exp (-((t - (1 / 2 : ℝ))⁻¹ ^ 4)) +
          Real.exp (-3 * ((1 - t)⁻¹ ^ 4))))
  else 0

end MathlibPlus.Analysis.Claim3081
