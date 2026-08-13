import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 11275: for the displayed one-prime Cayley impedance, the sign is
strictly negative under the exact hypotheses `t > 0`, `0 < q < 1`, and
`0 < θ < π`.  The source substitutions `q = p^(-σ)` and
`θ = τ * log p` are the parameter names represented by `q` and `θ` here. -/
theorem cayleyImpedance_negative_claim11275
    (q θ t : ℝ)
    (ht : 0 < t) (hq0 : 0 < q) (hq1 : q < 1)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    -q * Real.sin θ / (t * (1 - q * Real.cos θ)) < 0 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hinner : 0 < 1 - q * Real.cos θ := by
    have hmul : q * Real.cos θ ≤ q * 1 :=
      mul_le_mul_of_nonneg_left hcos (le_of_lt hq0)
    nlinarith
  have hden : 0 < t * (1 - q * Real.cos θ) :=
    mul_pos ht hinner
  have hnum : -q * Real.sin θ < 0 := by
    nlinarith [mul_pos hq0 hsin]
  exact div_neg_of_neg_of_pos hnum hden

end MathlibPlus.Analysis
