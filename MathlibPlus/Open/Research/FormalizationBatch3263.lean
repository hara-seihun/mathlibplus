import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

noncomputable section

open scoped BigOperators

/-- The de Bruijn--Newman theta kernel's nonnegative-side series. -/
noncomputable def thetaPhi3263 (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n then
      (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * t) -
          3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * t)) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * t))
    else 0

/-- The even de Bruijn--Newman theta kernel. -/
noncomputable def thetaKernel3263 (t : ℝ) : ℝ :=
  thetaPhi3263 |t|

/-- The confluent determinant flag associated with the kernel. -/
noncomputable def confluentFlag3263 (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      iteratedDeriv (i.val + j.val) thetaKernel3263 t)

/-- Global positivity of the confluent flag through order four. -/
def globalPositiveConfluentFlagThroughOrderFour3263 : Prop :=
  ∀ (t : ℝ) (m : ℕ), 1 ≤ m → m ≤ 4 → confluentFlag3263 m t > 0

end

end MathlibPlus.Open.Research.FormalizationBatch
