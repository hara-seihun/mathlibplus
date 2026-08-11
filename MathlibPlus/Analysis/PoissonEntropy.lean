import Mathlib

namespace MathlibPlus.Analysis.PoissonEntropy

/-- Claim 15643: the strict relative-entropy slope gap. -/
theorem strictPoissonRelativeEntropySlopeGap {d e : ℝ}
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    0 < e - d - d * Real.log (e / d) := by
  have hratio : 0 < e / d := div_pos he hd
  have hratio_ne : e / d ≠ 1 := by
    intro h
    apply hne
    exact ((div_eq_one_iff_eq hd.ne').mp h).symm
  have hlog := Real.log_lt_sub_one_of_pos hratio hratio_ne
  have hmul := mul_lt_mul_of_pos_left hlog hd
  calc
    0 < d * (e / d - 1 - Real.log (e / d)) := by nlinarith
    _ = e - d - d * Real.log (e / d) := by field_simp

end MathlibPlus.Analysis.PoissonEntropy
