import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim11285

/-- The explicit even polynomial from claim 11285. -/
def Y (z : ℂ) : ℂ :=
  (z ^ 2 + 1) ^ 2 * ((z ^ 2 + 1) ^ 2 + 1)

/-- The polynomial is even. -/
theorem Y_even_claim11285 : Function.Even Y := by
  intro z
  simp only [Y]
  ring

/-- On the real axis, `Y` is the displayed real polynomial. -/
theorem Y_ofReal_claim11285 (x : ℝ) :
    Y (x : ℂ) =
      ((x ^ 2 + 1) ^ 2 * ((x ^ 2 + 1) ^ 2 + 1) : ℝ) := by
  rw [Y]
  apply Complex.ext <;> norm_num

/-- The polynomial is strictly positive on the real axis. -/
theorem Y_positive_on_real_claim11285 (x : ℝ) : 0 < (Y (x : ℂ)).re := by
  rw [Y_ofReal_claim11285]
  change 0 < (x ^ 2 + 1) ^ 2 * ((x ^ 2 + 1) ^ 2 + 1)
  have h : 0 < x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hsq : 0 < (x ^ 2 + 1) ^ 2 := sq_pos_of_pos h
  have hplus : 0 < (x ^ 2 + 1) ^ 2 + 1 := by linarith
  exact mul_pos hsq hplus

/-- The squared-variable polynomial underlying `Y`. -/
def squaredY (w : ℂ) : ℂ :=
  (w + 1) ^ 2 * ((w + 1) ^ 2 + 1)

/-- `Y` is obtained from `squaredY` by substituting `z^2`. -/
theorem Y_eq_squaredY_claim11285 (z : ℂ) : Y z = squaredY (z ^ 2) := by
  rfl

/-- The two displayed off-axis squared zeros. -/
theorem squaredY_offAxisZeros_claim11285 :
    squaredY (-1 + Complex.I) = 0 ∧ squaredY (-1 - Complex.I) = 0 := by
  constructor
  · rw [squaredY]
    have h : (-1 + Complex.I + 1 : ℂ) = Complex.I := by ring
    rw [h, Complex.I_sq]
    norm_num
  · rw [squaredY]
    have h : (-1 - Complex.I + 1 : ℂ) = -Complex.I := by ring
    rw [h]
    have hi : (-Complex.I : ℂ) ^ 2 = -1 := by
      rw [neg_sq, Complex.I_sq]
    rw [hi]
    norm_num

/-- The displayed descended logarithmic derivative. -/
noncomputable def descendedLogDerivative (x : ℂ) : ℂ :=
  4 / (x + 1) + 2 / (x + 1 - Complex.I) + 2 / (x + 1 + Complex.I)

end MathlibPlus.Analysis.Claim11285
