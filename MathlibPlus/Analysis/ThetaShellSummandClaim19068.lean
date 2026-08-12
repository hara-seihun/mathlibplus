import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

noncomputable section

/-- The summand displayed in claim 19068. -/
def thetaShellSummand (m : ℕ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 * (m : ℝ) ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * (m : ℝ) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (4 * u))

/-- The literal summand in claim 19068 is positive for every positive integer
index and every nonnegative real parameter. -/
theorem thetaShellSummand_pos_claim19068 {m : ℕ} (hm : 0 < m) {u : ℝ}
    (hu : 0 ≤ u) :
    0 < thetaShellSummand m u := by
  rw [show thetaShellSummand m u =
      (Real.pi * (m : ℝ) ^ 2 * Real.exp (5 * u)) *
        (2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (4 * u) - 3) *
        Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (4 * u)) by
    dsimp [thetaShellSummand]
    rw [show Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) by
      rw [← Real.exp_add]
      congr 1 <;> ring]
    ring]
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hmpow : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hexp4 : (1 : ℝ) ≤ Real.exp (4 * u) :=
    Real.one_le_exp (by positivity)
  have hprod : (1 : ℝ) ≤ (m : ℝ) ^ 2 * Real.exp (4 * u) := by
    simpa using mul_le_mul hmpow hexp4 (by positivity) (by positivity)
  have hprodpos : 0 < (m : ℝ) ^ 2 * Real.exp (4 * u) := by positivity
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hmul : 3 * ((m : ℝ) ^ 2 * Real.exp (4 * u)) <
      Real.pi * ((m : ℝ) ^ 2 * Real.exp (4 * u)) :=
    mul_lt_mul_of_pos_right hpi hprodpos
  have hcoef : 0 < 2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (4 * u) - 3 := by
    nlinarith [hmul, hprod]
  positivity

end

end MathlibPlus.Analysis
