import Mathlib

/-!
# Arithmetic certificates from explicit analytic-number-theory claims

These declarations formalize the exact numerical and algebraic consequences in
admitted claims 1010, 1037, 1124, and 1218.  They do not assert any of the
analytic zero-free, de Bruijn--Newman, or zero-counting theorems that motivate
the certificates.
-/

namespace MathlibPlus.AnalyticNumberTheory.CertificateArithmetic

/-- The exact denominator and reciprocal-amplitude comparison from claim 1010. -/
theorem denominator48594_vs_4862 :
    (4.862 : ℝ) - 4.8594 = 13 / 5000 ∧
      (0 : ℝ) < 13 / 5000 ∧
      (1 / 4.8594 : ℝ) - 1 / 4.862 = 500 / 4543539 ∧
      (0 : ℝ) < 500 / 4543539 := by
  norm_num

/-- At every `t ≥ 2`, the real `σ`-half-plane for denominator `4.862` is
contained in the one for denominator `4.8594`.  This is the precise
set-theoretic meaning of the source's phrase "strictly wider". -/
theorem denominator48594_region_wider {t : ℝ} (ht : 2 ≤ t) :
    {σ : ℝ | 1 - 1 / (4.862 * Real.log t) < σ} ⊆
      {σ : ℝ | 1 - 1 / (4.8594 * Real.log t) < σ} := by
  intro σ hσ
  have hlog : 0 < Real.log t :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  have hsmall : 0 < (4.8594 : ℝ) * Real.log t := by
    positivity
  have hlarge : 0 < (4.862 : ℝ) * Real.log t := by
    positivity
  have hscale : (4.8594 : ℝ) * Real.log t < 4.862 * Real.log t := by
    nlinarith
  have hrecip : 1 / (4.862 * Real.log t) <
      1 / (4.8594 * Real.log t) := by
    exact one_div_lt_one_div_of_lt hsmall hscale
  have hboundary : 1 - 1 / (4.8594 * Real.log t) <
      1 - 1 / (4.862 * Real.log t) := by
    linarith
  exact lt_trans hboundary hσ

/-- The exact comparison and reserve between the two de Bruijn--Newman
numerical bounds in claim 1037. -/
theorem deBruijnNewman_bound_comparison :
    (7 / 40 : ℝ) = 35000000 / 200000000 ∧
      (7 / 40 : ℝ) < 37272481 / 200000000 ∧
      (37272481 / 200000000 : ℝ) - 7 / 40 =
        2272481 / 200000000 ∧
      (2272481 / 200000000 : ℝ) = 0.011362405 := by
  norm_num

/-- Any real quantity satisfying the stronger `7/40` bound satisfies the
`0.186362405` bound as well. -/
theorem deBruijnNewman_stronger_bound_implies_weaker {Λ : ℝ}
    (hΛ : Λ ≤ 7 / 40) :
    Λ ≤ 37272481 / 200000000 := by
  have h : (7 / 40 : ℝ) ≤ 37272481 / 200000000 := by
    norm_num
  exact hΛ.trans h

/-- The exact reciprocal-amplitude comparison from claim 1124. -/
theorem amplitude_51331_vs_5134 :
    (51.34 : ℝ) - 51.331 = 9 / 1000 ∧
      (1 / 51.331 : ℝ) - 1 / 51.34 = 450 / 131766677 ∧
      (0 : ℝ) < 450 / 131766677 := by
  norm_num

/-- Algebraic transfer of the retained `log (2π)` term in claim 1218.
The explicit hypothesis `1 ≤ T` records the stated range; the identity itself
uses no analytic property of `T` (or of `A`). -/
theorem retained_log_two_pi_normalization
    (A T C₁ B m N M : ℝ) (_hT : 1 ≤ T)
    (h : |N - M| ≤
      C₁ * ((Real.log A + m * Real.log T) - m * Real.log (2 * Real.pi)) +
        B * m) :
    |N - M| ≤
      C₁ * (Real.log A + m * Real.log T) +
        (B - C₁ * Real.log (2 * Real.pi)) * m := by
  calc
    |N - M| ≤
        C₁ * ((Real.log A + m * Real.log T) - m * Real.log (2 * Real.pi)) +
          B * m := h
    _ = C₁ * (Real.log A + m * Real.log T) +
          (B - C₁ * Real.log (2 * Real.pi)) * m := by
      ring

/-- Claim 1587: the displayed Bellotti--Wong leading coefficient arithmetic. -/
theorem leadingCoefficient_1587 (d a₁ C₁ : ℝ)
    (hd : d = 18 / 25) (ha₁ : a₁ = 2453 / 2500)
    (hC₁ : C₁ = d * a₁ / 4) :
    d = 0.720 ∧
      a₁ = 0.98120 ∧
      C₁ = 22077 / 125000 ∧
      C₁ = 0.176616 := by
  norm_num [hd, ha₁, hC₁]

/-- Claim 1588: the published decimal is strictly above the exact coefficient. -/
theorem roundedLeadingCoefficient_1588 (C₁ : ℝ)
    (hC₁ : C₁ = 22077 / 125000) :
    0.1767 - C₁ = 21 / 250000 ∧
      0 < 0.1767 - C₁ := by
  norm_num [hC₁]

end MathlibPlus.AnalyticNumberTheory.CertificateArithmetic
