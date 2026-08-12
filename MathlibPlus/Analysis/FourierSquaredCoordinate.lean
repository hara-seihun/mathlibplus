import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis.FourierSquaredCoordinate

/-!
Formalization of admitted claim 17582.  On the Fourier axis `s = i t`, the
factor `1 - 4*s^2` becomes `1 + 4*t^2`; for nonzero `t` this is not the
unrotated expression `1 - 4*t^2`.
-/

/-- The Fourier-axis rotation changes the sign of the squared coordinate. -/
theorem correctedFactor_17582 (t : ℝ) :
    (1 : ℂ) - 4 * ((t : ℂ) * Complex.I) ^ 2 = 1 + 4 * (t : ℂ) ^ 2 ∧
      (t ≠ 0 → (1 : ℂ) + 4 * (t : ℂ) ^ 2 ≠ 1 - 4 * (t : ℂ) ^ 2) := by
  constructor
  · rw [mul_pow, Complex.I_sq]
    ring
  · intro ht h
    have h' := congrArg Complex.re h
    have hreal : 1 + 4 * t ^ 2 = 1 - 4 * t ^ 2 := by
      simpa [pow_two, Complex.mul_re] using h'
    nlinarith [sq_pos_of_ne_zero ht]

end MathlibPlus.Analysis.FourierSquaredCoordinate
