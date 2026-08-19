import Mathlib

namespace MathlibPlus.Analysis.ClaimFormalizations

/-- Claim 15651: distinct positive critical slopes have negative relative rate. -/
theorem distinctPositiveSlopesNegativeRelativeRate
    (d e : ℝ) (hd : 0 < d) (he : 0 < e) (hde : d ≠ e) :
    (d - e + d * Real.log (e / d)) / 2 < 0 := by
  have hratio_pos : 0 < e / d := div_pos he hd
  have hratio_ne : e / d ≠ 1 := by
    intro h
    apply hde
    have h' : e = d := by
      apply (div_eq_one_iff_eq (ne_of_gt hd)).mp
      exact h
    exact h'.symm
  have hlog := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hscaled := mul_lt_mul_of_pos_left hlog hd
  have hscaled' : d * Real.log (e / d) < e - d := by
    calc
      d * Real.log (e / d) < d * (e / d - 1) := hscaled
      _ = e - d := by field_simp [ne_of_gt hd]
  nlinarith

end MathlibPlus.Analysis.ClaimFormalizations
