import Mathlib

namespace MathlibPlus.Analysis

/-- The standard raw logistic packet with scale `d`. -/
noncomputable def rawLogistic42081 (d x : ℝ) : ℝ :=
  (1 + Real.exp (-d * x))⁻¹

/-- The raw logistic derivative at the origin is `d/4`; hence a nonzero
scale cannot satisfy a zero-derivative endpoint premise. -/
theorem rawLogistic_deriv_claim42081 (d : ℝ) :
    HasDerivAt (rawLogistic42081 d) (d / 4) 0 ∧
      (d ≠ 0 → deriv (rawLogistic42081 d) 0 ≠ 0) := by
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      ((Real.hasDerivAt_exp ((-d) * (0 : ℝ))).comp 0
        ((hasDerivAt_id (0 : ℝ)).const_mul (-d)))).inv (by norm_num)
  have hlog : HasDerivAt (rawLogistic42081 d) (d / 4) 0 := by
    change HasDerivAt (fun x : ℝ => (1 + Real.exp (-d * x))⁻¹) (d / 4) 0
    convert h using 1
    all_goals try rfl
    all_goals simp only [Pi.add_apply, Function.comp_apply, Real.exp_zero,
      mul_zero, mul_one, zero_add, one_mul]
    all_goals ring
  refine ⟨hlog, ?_⟩
  intro hd
  rw [hlog.deriv]
  exact div_ne_zero hd (by norm_num)

end MathlibPlus.Analysis
