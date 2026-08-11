import Mathlib

/-!
# Goldbach auxiliary cubic identity

Statement-faithful formalization of admitted claim 13010. The source's `e` is
Euler's number, represented here as `Real.exp 1`, and the fractional powers are
real powers.
-/

namespace MathlibPlus.Analysis.GoldbachAuxiliary

/-- Claim 13010: the displayed logarithmic auxiliary function has the stated
cubic value and exponential reparameterization. -/
theorem goldbachAuxiliaryCubicIdentity (x : ℝ) (hx : Real.exp 1 < x) :
    let V : ℝ :=
      (Real.log x) ^ (2 / 3 : ℝ) * (Real.log (Real.log x)) ^ (1 / 3 : ℝ)
    let y : ℝ := Real.log x
    let z : ℝ := 2 * Real.log y
    V ^ (3 : ℕ) = y ^ 2 * Real.log y ∧
      y ^ 2 * Real.log y = (1 / 2 : ℝ) * z * Real.exp z := by
  dsimp
  have hxpos : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hyone : 1 < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx
  have hypos : 0 < Real.log x := lt_trans zero_lt_one hyone
  have hlogypos : 0 < Real.log (Real.log x) := Real.log_pos hyone
  have hA :
      (Real.log x ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = Real.log x ^ (2 : ℕ) := by
    calc
      (Real.log x ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
          (Real.log x ^ (2 / 3 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (Real.log x ^ (2 / 3 : ℝ)) 3).symm
      _ = Real.log x ^ ((2 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hypos.le _ _).symm
      _ = Real.log x ^ (2 : ℝ) := by norm_num
      _ = Real.log x ^ (2 : ℕ) := Real.rpow_natCast (Real.log x) 2
  have hB :
      (Real.log (Real.log x) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
        Real.log (Real.log x) := by
    calc
      (Real.log (Real.log x) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
          (Real.log (Real.log x) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (Real.log (Real.log x) ^ (1 / 3 : ℝ)) 3).symm
      _ = Real.log (Real.log x) ^ ((1 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hlogypos.le _ _).symm
      _ = Real.log (Real.log x) ^ (1 : ℝ) := by norm_num
      _ = Real.log (Real.log x) := Real.rpow_one _
  constructor
  · rw [mul_pow, hA, hB]
  · have hexp :
        Real.exp (2 * Real.log (Real.log x)) = Real.log x ^ (2 : ℕ) := by
      have h := Real.exp_nat_mul (Real.log (Real.log x)) 2
      rw [Real.exp_log hypos] at h
      simpa using h
    rw [hexp]
    ring

end MathlibPlus.Analysis.GoldbachAuxiliary
