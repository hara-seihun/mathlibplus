import Mathlib.Tactic

namespace MathlibPlus.Analysis

/--
Claim 47834 (R-3684): the centered Euler coefficient `b_p = -(p + 1)`
falls strictly outside the positive-Gram interval for every integer `p > 1`.
The source does not assume that `p` is prime at this statement's scope.
-/
theorem claim47834_centeredEulerCoefficient_tempered_bound (p : ℕ) (hp : 1 < p) :
    let b : ℝ := -((p : ℝ) + 1)
    |b| = (p : ℝ) + 1 ∧
      (p : ℝ) + 1 > 2 * Real.sqrt (p : ℝ) := by
  dsimp
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hsq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by
    rw [Real.sq_sqrt (le_of_lt hp0)]
  have hsqrt : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hpgt : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  have hsqrt_ne : Real.sqrt (p : ℝ) ≠ 1 := by
    intro h
    nlinarith [hsq]
  have hsqpos : 0 < (Real.sqrt (p : ℝ) - 1) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hsqrt_ne)
  constructor
  · rw [abs_of_nonpos]
    · ring
    · exact neg_nonpos.mpr (by positivity)
  · nlinarith

end MathlibPlus.Analysis
