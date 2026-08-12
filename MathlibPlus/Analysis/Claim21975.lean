import Mathlib

namespace MathlibPlus.Analysis.Claim21975

/-!
# Riemann--Siegel correction charges

Formalization of admitted claim 21975.  The correction and its first two
formal derivatives are represented by `r`, `r₁`, and `r₂`; the multiplier and
its first two derivatives are `Q`, `Q₁`, and `Q₂`.  The source's pointwise
bounds and product-rule interface are explicit, and the three budget additions
are proved as absolute-value bounds rather than copied definitions.
-/

/-- Product-rule propagation of pointwise correction bounds through the
Riemann--Siegel multiplier, with the three exact budget charges. -/
theorem correctionChargeBounds
    (Q Q₁ Q₂ r r₁ r₂ : ℝ → ℝ) (Q₀ q₁₀ q₂₀ e₀ e₁ e₂ t : ℝ)
    (hQ₀ : 0 ≤ Q₀) (hq₁₀ : 0 ≤ q₁₀) (hq₂₀ : 0 ≤ q₂₀)
    (hQ : |Q t| ≤ Q₀)
    (hQ₁ : |Q₁ t| ≤ Q₀ * q₁₀)
    (hQ₂ : |Q₂ t| ≤ Q₀ * (q₁₀ ^ 2 + q₂₀))
    (hr : |r t| ≤ e₀)
    (hr₁ : |r₁ t| ≤ e₁)
    (hr₂ : |r₂ t| ≤ e₂)
    (hQderiv : HasDerivAt Q (Q₁ t) t)
    (hQ₁deriv : HasDerivAt Q₁ (Q₂ t) t)
    (hrderiv : HasDerivAt r (r₁ t) t)
    (hr₁deriv : HasDerivAt r₁ (r₂ t) t) :
    HasDerivAt (Q * r)
        (Q₁ t * r t + Q t * r₁ t) t ∧
      HasDerivAt (Q₁ * r + Q * r₁)
        (Q₂ t * r t + Q₁ t * r₁ t + (Q₁ t * r₁ t + Q t * r₂ t)) t ∧
      |Q t * r t| ≤ Q₀ * e₀ ∧
      |Q₁ t * r t + Q t * r₁ t| ≤ Q₀ * (e₁ + q₁₀ * e₀) ∧
      |Q₂ t * r t + 2 * Q₁ t * r₁ t + Q t * r₂ t| ≤
        Q₀ * (e₂ + 2 * q₁₀ * e₁ + (q₁₀ ^ 2 + q₂₀) * e₀) := by
  have hprod₁ : HasDerivAt (Q * r)
      (Q₁ t * r t + Q t * r₁ t) t := by
    simpa only [Pi.mul_apply] using hQderiv.mul hrderiv
  have hprod₂ : HasDerivAt (Q₁ * r + Q * r₁)
      (Q₂ t * r t + Q₁ t * r₁ t + (Q₁ t * r₁ t + Q t * r₂ t)) t := by
    simpa only [Pi.add_apply, Pi.mul_apply] using
      (hQ₁deriv.mul hrderiv).add (hQderiv.mul hr₁deriv)
  have hmul0 : |Q t * r t| ≤ Q₀ * e₀ := by
    rw [abs_mul]
    exact mul_le_mul hQ hr (abs_nonneg _) hQ₀
  have hmul₁ : |Q₁ t * r t| ≤ (Q₀ * q₁₀) * e₀ := by
    rw [abs_mul]
    exact mul_le_mul hQ₁ hr (abs_nonneg _) (mul_nonneg hQ₀ hq₁₀)
  have hmul₂ : |Q t * r₁ t| ≤ Q₀ * e₁ := by
    rw [abs_mul]
    exact mul_le_mul hQ hr₁ (abs_nonneg _) hQ₀
  have hfirst : |Q₁ t * r t + Q t * r₁ t| ≤
      Q₀ * (e₁ + q₁₀ * e₀) := by
    calc
      |Q₁ t * r t + Q t * r₁ t| ≤
          |Q₁ t * r t| + |Q t * r₁ t| := abs_add_le _ _
      _ ≤ (Q₀ * q₁₀) * e₀ + Q₀ * e₁ := add_le_add hmul₁ hmul₂
      _ = Q₀ * (e₁ + q₁₀ * e₀) := by ring
  have hmul₃ : |Q₂ t * r t| ≤ (Q₀ * (q₁₀ ^ 2 + q₂₀)) * e₀ := by
    rw [abs_mul]
    exact mul_le_mul hQ₂ hr (abs_nonneg _)
      (mul_nonneg hQ₀ (add_nonneg (sq_nonneg _) hq₂₀))
  have hmul₄ : |2 * Q₁ t * r₁ t| ≤ 2 * (Q₀ * q₁₀) * e₁ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul hQ₁ hr₁ (abs_nonneg _) (mul_nonneg hQ₀ hq₁₀)
    nlinarith
  have hmul₅ : |Q t * r₂ t| ≤ Q₀ * e₂ := by
    rw [abs_mul]
    exact mul_le_mul hQ hr₂ (abs_nonneg _) hQ₀
  have hsecond :
      |Q₂ t * r t + 2 * Q₁ t * r₁ t + Q t * r₂ t| ≤
        Q₀ * (e₂ + 2 * q₁₀ * e₁ + (q₁₀ ^ 2 + q₂₀) * e₀) := by
    calc
      |Q₂ t * r t + 2 * Q₁ t * r₁ t + Q t * r₂ t| ≤
          |Q₂ t * r t| + |2 * Q₁ t * r₁ t| + |Q t * r₂ t| := by
            calc
              |Q₂ t * r t + 2 * Q₁ t * r₁ t + Q t * r₂ t| ≤
                  |Q₂ t * r t + 2 * Q₁ t * r₁ t| + |Q t * r₂ t| :=
                    abs_add_le _ _
              _ ≤ (|Q₂ t * r t| + |2 * Q₁ t * r₁ t|) + |Q t * r₂ t| := by
                    gcongr
                    exact abs_add_le _ _
              _ = |Q₂ t * r t| + |2 * Q₁ t * r₁ t| + |Q t * r₂ t| := by ring
      _ ≤ (Q₀ * (q₁₀ ^ 2 + q₂₀)) * e₀ +
            2 * (Q₀ * q₁₀) * e₁ + Q₀ * e₂ := by
            gcongr
      _ = Q₀ * (e₂ + 2 * q₁₀ * e₁ + (q₁₀ ^ 2 + q₂₀) * e₀) := by ring
  exact ⟨hprod₁, hprod₂, hmul0, hfirst, hsecond⟩

end MathlibPlus.Analysis.Claim21975
