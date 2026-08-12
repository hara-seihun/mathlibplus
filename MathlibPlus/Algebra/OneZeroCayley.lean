import Mathlib

namespace MathlibPlus.Algebra

/-- The exact one-zero Cayley identity from O-0131/O-0295.  The hypotheses
record precisely the points at which the displayed rational expressions are
undefined. -/
theorem oneZeroCayleyIdentity
    {γ t : ℝ} {z : ℂ}
    (hγ : (γ : ℂ) ≠ 0)
    (hz : z ≠ 0)
    (hquad : z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2 ≠ 0)
    (hleft :
      1 + (z - (t : ℂ) ^ 2 / z - 2 * Complex.I * (t : ℂ)) /
          (γ : ℂ) ^ 2 ≠ 0)
    (hright :
      1 - Complex.I * (t : ℂ) *
          (2 * z / (z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2)) ≠ 0) :
    (1 + (z - (t : ℂ) ^ 2 / z + 2 * Complex.I * (t : ℂ)) /
          (γ : ℂ) ^ 2) /
        (1 + (z - (t : ℂ) ^ 2 / z - 2 * Complex.I * (t : ℂ)) /
          (γ : ℂ) ^ 2) =
      (1 + Complex.I * (t : ℂ) *
          (2 * z / (z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2))) /
        (1 - Complex.I * (t : ℂ) *
          (2 * z / (z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2))) := by
  have hγpow : (γ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hγ
  have hquad' :
      z * (γ : ℂ) ^ 2 + z ^ 2 - (t : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply hquad
    calc
      z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2 =
          z * (γ : ℂ) ^ 2 + z ^ 2 - (t : ℂ) ^ 2 := by ring
      _ = 0 := h
  have hquad'' :
      z * (z + (γ : ℂ) ^ 2) - (t : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply hquad
    calc
      z ^ 2 + (γ : ℂ) ^ 2 * z - (t : ℂ) ^ 2 =
          z * (z + (γ : ℂ) ^ 2) - (t : ℂ) ^ 2 := by ring
      _ = 0 := h
  apply (div_eq_div_iff hleft hright).2
  field_simp [hγpow, hz, hquad, hquad', hquad'']
  ring

end MathlibPlus.Algebra
