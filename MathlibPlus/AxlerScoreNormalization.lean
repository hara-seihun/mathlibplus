import Mathlib

/-!
# Axler-score normalization

Statement-faithful algebraic formalization of admitted claim 1331 from packet
`C-0089`. `piValue` stands for the positive value `π(x)`, avoiding a duplicate
real prime-counting definition.
-/

namespace MathlibPlus.AxlerScoreNormalization

/-- On the packet's positive domain, the strict Axler denominator bound is
exactly equivalent to its pole-cancelled score inequality. -/
theorem bound_iff_score_lt (x c piValue : ℝ) (hx : 1 < x)
    (hpi : 0 < piValue) (hden : 0 < Real.log x - 1 - c / Real.log x) :
    piValue < x / (Real.log x - 1 - c / Real.log x) ↔
      Real.log x * (Real.log x - 1 - x / piValue) < c := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlog
  have hid :
      Real.log x * (Real.log x - 1 - x / piValue) - c =
        Real.log x *
          ((Real.log x - 1 - c / Real.log x) - x / piValue) := by
    field_simp [hlogne]
    ring
  constructor
  · intro h
    have hcross : piValue * (Real.log x - 1 - c / Real.log x) < x :=
      (lt_div_iff₀ hden).mp h
    have hquot : Real.log x - 1 - c / Real.log x < x / piValue := by
      apply (lt_div_iff₀ hpi).2
      nlinarith
    have hprod :
        Real.log x *
            ((Real.log x - 1 - c / Real.log x) - x / piValue) < 0 :=
      mul_neg_of_pos_of_neg hlog (sub_neg.mpr hquot)
    rw [← hid] at hprod
    linarith
  · intro h
    have hprod :
        Real.log x *
            ((Real.log x - 1 - c / Real.log x) - x / piValue) < 0 := by
      rw [← hid]
      linarith
    have hdiff :
        (Real.log x - 1 - c / Real.log x) - x / piValue < 0 := by
      by_contra hnot
      have hnonneg :
          0 ≤ (Real.log x - 1 - c / Real.log x) - x / piValue :=
        le_of_not_gt hnot
      exact (not_le_of_gt hprod) (mul_nonneg (le_of_lt hlog) hnonneg)
    have hquot : Real.log x - 1 - c / Real.log x < x / piValue :=
      sub_neg.mp hdiff
    have hcross : (Real.log x - 1 - c / Real.log x) * piValue < x :=
      (lt_div_iff₀ hpi).mp hquot
    apply (lt_div_iff₀ hden).2
    nlinarith

end MathlibPlus.AxlerScoreNormalization
