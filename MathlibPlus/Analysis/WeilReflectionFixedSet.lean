import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The fixed set of the Weil reflection `s ↦ 1 - conj s` is the critical
line. -/
theorem claim4856_weil_reflection_fixed (s : ℂ) :
    (1 - starRingEnd ℂ s = s) ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring_nf

end MathlibPlus.Analysis
