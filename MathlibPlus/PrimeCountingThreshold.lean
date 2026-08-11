import Mathlib

/-!
# Prime-counting denominator threshold

Statement-faithful algebraic formalization of admitted claim 1167 from packet
`C-0078`. The positive real parameter `piValue` is the value `π(x)`; stating the
identity parametrically avoids introducing a duplicate prime-counting definition.
-/

namespace MathlibPlus.PrimeCountingThreshold

/-- For a positive prime-counting value and positive logarithmic denominator,
the strict denominator bound is equivalent to the packet's threshold-score
inequality `log x - x / π(x) < c`. -/
theorem bound_iff_score_lt (x c piValue : ℝ) (hpi : 0 < piValue)
    (hc : c < Real.log x) :
    piValue < x / (Real.log x - c) ↔
      Real.log x - x / piValue < c := by
  have hden : 0 < Real.log x - c := sub_pos.mpr hc
  constructor
  · intro h
    have hcross : piValue * (Real.log x - c) < x :=
      (lt_div_iff₀ hden).mp h
    have hquot : Real.log x - c < x / piValue := by
      apply (lt_div_iff₀ hpi).2
      nlinarith
    linarith
  · intro h
    have hquot : Real.log x - c < x / piValue := by linarith
    have hcross : (Real.log x - c) * piValue < x :=
      (lt_div_iff₀ hpi).mp hquot
    apply (lt_div_iff₀ hden).2
    nlinarith

end MathlibPlus.PrimeCountingThreshold
