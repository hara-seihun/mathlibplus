import Mathlib

namespace MathlibPlus.Analysis.Claim19307

/-!
Formalization of the displayed inequality in admitted claim 19307.  The
source's named shell function `ℓ_λ` is not defined in the claim record, so its
stated value at `3` is inlined exactly.
-/

/-- For every `ell ≥ π`, the displayed shell value at `3` is strictly negative. -/
theorem shellParameterNegative {ell : ℝ} (hell : Real.pi ≤ ell) :
    (37 / 64 : ℝ) - (3 / 16) * ell * Real.exp 6 < 0 := by
  have hpi : (3 : ℝ) < Real.pi := by
    exact Real.pi_gt_three
  have hell3 : (3 : ℝ) < ell := lt_of_lt_of_le hpi hell
  have hexp : (7 : ℝ) ≤ Real.exp 6 := by
    have h := Real.add_one_le_exp (6 : ℝ)
    norm_num at h ⊢
    exact h
  nlinarith [Real.exp_pos (6 : ℝ)]

end MathlibPlus.Analysis.Claim19307
