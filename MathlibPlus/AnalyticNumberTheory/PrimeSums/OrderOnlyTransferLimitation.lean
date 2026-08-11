import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.PrimeSums

/-- The scalar counterexample behind claim 775 rules out both order-only
transfers from an upper bound and from a symmetric absolute bound. -/
theorem orderOnlyThetaPsiTransferLimitation :
    ((-2 : ℝ) ≤ -1 ∧
      (-1 : ℝ) ≤ 1 ∧
      |(-1 : ℝ)| ≤ 1 ∧
      1 < |(-2 : ℝ)|) ∧
    (¬ (∀ a b : ℝ, a ≤ b → b ≤ 1 → |a| ≤ 1)) ∧
    (¬ (∀ a b : ℝ, a ≤ b → |b| ≤ 1 → |a| ≤ 1)) := by
  constructor
  · norm_num
  constructor
  · intro h
    have h' := h (-2 : ℝ) (-1 : ℝ) (by norm_num) (by norm_num)
    norm_num at h'
  · intro h
    have h' := h (-2 : ℝ) (-1 : ℝ) (by norm_num) (by norm_num)
    norm_num at h'

end MathlibPlus.AnalyticNumberTheory.PrimeSums
