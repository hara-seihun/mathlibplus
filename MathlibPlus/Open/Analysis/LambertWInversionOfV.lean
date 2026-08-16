import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The principal real branch on the positive real axis, characterized by its
nonnegative solution of `w * exp w = z`. -/
noncomputable def principalLambertW (z : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = z}

/-- Exact open formalization of the admitted Lambert-W inversion claim. -/
def lambertWInversionOfV : Prop :=
  ∀ A x : ℝ,
    0 < A → Real.exp 1 < x →
      ((Real.log x) ^ (2 / 3 : ℝ) * (Real.log (Real.log x)) ^ (1 / 3 : ℝ) = A ↔
        Real.log (Real.log x) = (1 / 2 : ℝ) * principalLambertW (2 * A ^ 3))

end MathlibPlus.Open.Analysis
