import Mathlib

namespace MathlibPlus.Analysis.Claim59082

/-- The exact algebraic scaling consequence in claim 59082, with the
complementary-cone convention made explicit in the angle hypothesis. -/
theorem orderScaling
    {δ : ℝ} {N m : ℕ}
    (hδpos : 0 < δ) (_hδpi : δ < Real.pi)
    (hN : 1 ≤ N)
    (hangle : Real.pi - Real.pi * (m : ℝ) /
        ((N : ℝ) + (m : ℝ) - 1) ≤ δ) :
    ((1 - δ / Real.pi) / (δ / Real.pi)) * ((N : ℝ) - 1) ≤ (m : ℝ) := by
  by_cases hN1 : N = 1
  · subst N
    norm_num
  · have hN2 : 2 ≤ N := by omega
    have hden : 0 < (N : ℝ) + (m : ℝ) - 1 := by
      have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hangle' :
        1 - (m : ℝ) / ((N : ℝ) + (m : ℝ) - 1) ≤ δ / Real.pi := by
      calc
        1 - (m : ℝ) / ((N : ℝ) + (m : ℝ) - 1) =
            (Real.pi - Real.pi * (m : ℝ) /
              ((N : ℝ) + (m : ℝ) - 1)) / Real.pi := by
                field_simp [ne_of_gt hpi, ne_of_gt hden]
        _ ≤ δ / Real.pi := by
          exact (div_le_div_of_nonneg_right hangle (le_of_lt hpi))
    have hfrac :
        1 - δ / Real.pi ≤ (m : ℝ) /
          ((N : ℝ) + (m : ℝ) - 1) := by linarith
    have hbound :
        (1 - δ / Real.pi) * ((N : ℝ) + (m : ℝ) - 1) ≤ (m : ℝ) :=
      (le_div_iff₀ hden).mp hfrac
    have ht : 0 < δ / Real.pi := div_pos hδpos hpi
    have hcross :
        (1 - δ / Real.pi) * ((N : ℝ) - 1) ≤
          (δ / Real.pi) * (m : ℝ) := by
      nlinarith [hbound]
    calc
      ((1 - δ / Real.pi) / (δ / Real.pi)) * ((N : ℝ) - 1) =
          ((1 - δ / Real.pi) * ((N : ℝ) - 1)) / (δ / Real.pi) := by ring
      _ ≤ (m : ℝ) := by
        exact (div_le_iff₀ ht).2 (by simpa [mul_comm] using hcross)

end MathlibPlus.Analysis.Claim59082
