import Mathlib

namespace MathlibPlus.Analysis

/-! Kernel-checked elementary transfer and normalization facts for admitted
claims 795 and 806. -/

/-- Claim 795: a smaller amplitude and a larger decay coefficient move an
upper envelope in the safe direction. -/
theorem amplitudeDecayComparisonTransfer :
    ∀ L c C D d : ℝ, 0 ≤ L → 0 ≤ c → c ≤ C → D ≤ d →
      c * Real.exp (-d * Real.sqrt L) ≤
        C * Real.exp (-D * Real.sqrt L) := by
  intro L c C D d hL hc hcc hDd
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hde : Real.exp (-d * Real.sqrt L) ≤
      Real.exp (-D * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hDd hsqrt
    linarith
  calc
    c * Real.exp (-d * Real.sqrt L) ≤
        C * Real.exp (-d * Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hcc (le_of_lt (Real.exp_pos _))
    _ ≤ C * Real.exp (-D * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hde (le_trans hc hcc)

/-- Claim 806: the absolute normalized psi error is the absolute numerator
 divided by the positive denominator. -/
theorem absoluteChebyshevPsiErrorNormalization :
    ∀ x : ℝ, 0 < x →
      |(Chebyshev.psi x - x) / x| = |Chebyshev.psi x - x| / x := by
  intro x hx
  rw [abs_div, abs_of_pos hx]

end MathlibPlus.Analysis
