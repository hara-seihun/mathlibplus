import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-!
Claim 15267 does not state the ambient domains or the relation between `c`, `d`,
and `δ` in isolation.  This formalization makes the displayed logarithmic
regime explicit: `d` and `δ` are positive, `c = d + δ`, and `2δ < 1`.
-/

/-- Claim 15267: in the stated positive regime, the logarithmic gain is
strictly below the reciprocal linear bound for every `r ≥ 1`. -/
theorem claim15267_gain_beyond_zero_saddle
    (E : ℝ → ℝ) (c d δ : ℝ)
    (hd : 0 < d) (hδ : 0 < δ) (hδsmall : 2 * δ < 1)
    (hc : c = d + δ)
    (hE : ∀ r : ℝ, 1 ≤ r → E r = 2 * Real.log (c / d)) :
    0 < 1 / d - 2 * Real.log (c / d) ∧
      ∀ r : ℝ, 1 ≤ r → E r < r / d := by
  have hpos : 0 < 1 + δ / d := by positivity
  have hδd : 0 < δ / d := div_pos hδ hd
  have hne : 1 + δ / d ≠ 1 := by linarith
  have hlog : Real.log (1 + δ / d) < δ / d := by
    have h := Real.log_lt_sub_one_of_pos hpos hne
    simpa using h
  have hmul : 2 * d * Real.log (1 + δ / d) < 2 * δ := by
    calc
      2 * d * Real.log (1 + δ / d) < 2 * d * (δ / d) :=
        mul_lt_mul_of_pos_left hlog (show 0 < 2 * d by positivity)
      _ = 2 * δ := by field_simp [ne_of_gt hd]
  have hsmall : 2 * d * Real.log (1 + δ / d) < 1 :=
    lt_trans hmul hδsmall
  have hlogcd : Real.log (c / d) = Real.log (1 + δ / d) := by
    congr 1
    rw [hc]
    field_simp [ne_of_gt hd]
  have hcore : 2 * Real.log (c / d) < 1 / d := by
    rw [hlogcd]
    apply (lt_div_iff₀ hd).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsmall
  constructor
  · exact sub_pos.mpr hcore
  · intro r hr
    rw [hE r hr]
    exact lt_of_lt_of_le hcore (div_le_div_of_nonneg_right hr hd.le)

end MathlibPlus.Analysis
