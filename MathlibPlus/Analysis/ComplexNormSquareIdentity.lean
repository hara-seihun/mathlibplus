import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis.ComplexNormSquare

/--
Claim 42860: exact norm-square identity for a paired complex factor on a
real height.  The source's absolute-value notation is represented by the
complex norm, and the real height is explicitly coerced to `ℂ`.
-/
theorem normSq_vertical_factor_claim42860 (ρ : ℂ) (hρ : ρ ≠ 0) (h : ℝ) :
    ‖(1 : ℂ) + (h ^ 2 : ℂ) / ρ ^ 2‖ ^ 2 =
      1 + h ^ 2 * (h ^ 2 + 2 * (ρ.re ^ 2 - ρ.im ^ 2)) / ‖ρ‖ ^ 4 := by
  have hrewrite :
      (1 : ℂ) + (h ^ 2 : ℂ) / ρ ^ 2 =
        (ρ ^ 2 + (h ^ 2 : ℂ)) / ρ ^ 2 := by
    field_simp [hρ]
  have hnum :
      Complex.normSq (ρ ^ 2 + (h ^ 2 : ℂ)) =
        (ρ.re ^ 2 - ρ.im ^ 2 + h ^ 2) ^ 2 +
          (2 * ρ.re * ρ.im) ^ 2 := by
    simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
    ring_nf
  have hden : Complex.normSq (ρ ^ 2) = ‖ρ‖ ^ 4 := by
    rw [map_pow, Complex.normSq_eq_norm_sq]
    ring
  have hnorm4 : ‖ρ‖ ^ 4 = (ρ.re ^ 2 + ρ.im ^ 2) ^ 2 := by
    rw [show ‖ρ‖ ^ 4 = (‖ρ‖ ^ 2) ^ 2 by ring, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hsum : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by
    have hs := (Complex.normSq_pos.mpr hρ)
    rw [Complex.normSq_apply] at hs
    nlinarith
  have hdenom : (ρ.re ^ 2 + ρ.im ^ 2) ^ 2 ≠ 0 := by
    positivity
  calc
    ‖(1 : ℂ) + (h ^ 2 : ℂ) / ρ ^ 2‖ ^ 2 =
        Complex.normSq ((1 : ℂ) + (h ^ 2 : ℂ) / ρ ^ 2) := Complex.sq_norm _
    _ = Complex.normSq ((ρ ^ 2 + (h ^ 2 : ℂ)) / ρ ^ 2) := by rw [hrewrite]
    _ = Complex.normSq (ρ ^ 2 + (h ^ 2 : ℂ)) / Complex.normSq (ρ ^ 2) :=
      Complex.normSq_div _ _
    _ = 1 + h ^ 2 * (h ^ 2 + 2 * (ρ.re ^ 2 - ρ.im ^ 2)) / ‖ρ‖ ^ 4 := by
      rw [hnum, hden, hnorm4]
      field_simp [hdenom]
      ring

end MathlibPlus.Analysis.ComplexNormSquare
