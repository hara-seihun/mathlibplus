import Mathlib

namespace MathlibPlus.Algebra.Claim12994

/-- The squared roots of the quadratic in the quartic counterexample. -/
theorem quarticSquaredRoots :
    ((-3 : ℂ) + 4 * Complex.I)^2 + 6 * ((-3 : ℂ) + 4 * Complex.I) + 25 = 0 ∧
      ((-3 : ℂ) - 4 * Complex.I)^2 + 6 * ((-3 : ℂ) - 4 * Complex.I) + 25 = 0 := by
  constructor <;> ring_nf <;> simp [Complex.I_sq]

/-- Both signs give a nonreal denominator zero with nonzero numerator. -/
theorem impedancePoleWitness (t : ℝ) (ht0 : 0 < t) (ht2 : t < 2)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let q₀ : ℂ := (-3 : ℂ) + 2 * Complex.I * (ε : ℂ) * (Real.sqrt (4 - t^2) : ℂ)
    (q₀.im ≠ 0) ∧
      ((q₀ + 3)^2 + 16 - 4 * (t : ℂ)^2 = 0) ∧
        (4 * (q₀ + 3) ≠ 0) := by
  dsimp
  have hpos : 0 < 4 - t^2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (4 - t^2) := Real.sqrt_pos.2 hpos
  have hsqrt_sq : (Real.sqrt (4 - t^2))^2 = 4 - t^2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hsqrt_sq_c : ((Real.sqrt (4 - t^2) : ℂ)^2) = (4 - t^2 : ℂ) := by
    exact_mod_cast hsqrt_sq
  have hε0 : ε ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  have hεsq : ε ^ 2 = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have hεc : (ε : ℂ)^2 = 1 := by
    exact_mod_cast hεsq
  constructor
  · intro hzero
    have hnonzero : (2 : ℝ) * ε * Real.sqrt (4 - t^2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hε0) (ne_of_gt hsqrt)
    apply hnonzero
    simpa [Complex.mul_im] using hzero
  constructor
  · rw [show ((-3 : ℂ) + 2 * Complex.I * (ε : ℂ) * (Real.sqrt (4 - t^2) : ℂ) + 3)^2 =
        (2 * Complex.I * (ε : ℂ) * (Real.sqrt (4 - t^2) : ℂ))^2 by ring]
    rw [show (2 * Complex.I * (ε : ℂ) * (Real.sqrt (4 - t^2) : ℂ))^2 =
        -4 * (ε : ℂ)^2 * (Real.sqrt (4 - t^2) : ℂ)^2 by
          rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
          norm_num]
    rw [hsqrt_sq_c, hεc]
    ring
  · intro hzero
    have hprod : (ε : ℂ) * (Real.sqrt (4 - t^2) : ℂ) = 0 := by
      apply_fun (fun z : ℂ => z / (8 * Complex.I)) at hzero
      simpa [div_eq_mul_inv] using hzero
    rcases mul_eq_zero.mp hprod with hεc | hsc
    · exact hε0 (Complex.ofReal_eq_zero.mp hεc)
    · exact (ne_of_gt hsqrt) (Complex.ofReal_eq_zero.mp hsc)

end MathlibPlus.Algebra.Claim12994
