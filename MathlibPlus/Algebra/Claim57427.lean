import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim57427

/-!
The source also mentions rank-one and rank-two inequalities, but does not give
those expressions.  This declaration formalizes the fully specified D3
rank-three polynomial, its decreasing p-derivative on the stated interval, and
its positive endpoint minimum.
-/

/-- The displayed D3 rank-three polynomial is minimized at `p = s^2 / 4` on
`0 ≤ p ≤ s^2 / 4`, and that minimum is positive for `s ≥ 4`. -/
theorem d3Restoration_rankThree_claim57427
    (s p : ℝ) (hs : 4 ≤ s) (hp : 0 ≤ p) (hpmax : p ≤ s ^ 2 / 4) :
    let Φ : ℝ → ℝ := fun t =>
      s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
        108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * t + 144 * t ^ 2
    (-12 * s * (s ^ 2 + 9 * s - 22) + 288 * p < 0) ∧
      Φ (s ^ 2 / 4) ≤ Φ p ∧
      Φ (s ^ 2 / 4) =
        s * (s ^ 5 + 12 * s ^ 4 + 49 * s ^ 3 + 87 * s ^ 2 + 148 * s - 108) ∧
      0 < Φ (s ^ 2 / 4) := by
  dsimp
  have hs0 : 0 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hs4 : 0 ≤ s - 4 := by linarith
  have hs7 : 0 ≤ s + 7 := by linarith
  have hquad : 0 < s ^ 2 + 3 * s - 22 := by
    nlinarith [mul_nonneg hs4 hs7]
  have hderivative : ∀ t : ℝ, 0 ≤ t → t ≤ s ^ 2 / 4 →
      -12 * s * (s ^ 2 + 9 * s - 22) + 288 * t < 0 := by
    intro t ht htmax
    have hbound : 288 * t ≤ 72 * s ^ 2 := by
      nlinarith
    have hnegative : -12 * s * (s ^ 2 + 3 * s - 22) < 0 := by
      nlinarith [mul_pos hspos hquad]
    nlinarith
  have hderiv_p := hderivative p hp hpmax
  have hp0 : 0 ≤ s ^ 2 / 4 := by positivity
  have hderiv_endpoint := hderivative (s ^ 2 / 4) hp0 (by rfl)
  have hfac :
      144 * (p + s ^ 2 / 4) - 12 * s * (s ^ 2 + 9 * s - 22) < 0 := by
    nlinarith [hderiv_endpoint]
  have hleft : p - s ^ 2 / 4 ≤ 0 := by linarith
  have hdiff : 0 ≤
      (p - s ^ 2 / 4) *
        (144 * (p + s ^ 2 / 4) - 12 * s * (s ^ 2 + 9 * s - 22)) := by
    exact mul_nonneg_of_nonpos_of_nonpos hleft (le_of_lt hfac)
  have hfactor :
      (s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
          108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * p + 144 * p ^ 2) -
        (s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
          108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * (s ^ 2 / 4) +
            144 * (s ^ 2 / 4) ^ 2) =
      (p - s ^ 2 / 4) *
        (144 * (p + s ^ 2 / 4) - 12 * s * (s ^ 2 + 9 * s - 22)) := by
    ring
  have hminimum :
      s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
          108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * (s ^ 2 / 4) +
            144 * (s ^ 2 / 4) ^ 2 ≤
        s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
          108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * p + 144 * p ^ 2 := by
    nlinarith [hfactor, hdiff]
  have hs5 : (4 : ℝ) ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (by norm_num) hs 5
  have hs5' : (1024 : ℝ) ≤ s ^ 5 := by norm_num at hs5 ⊢; exact hs5
  have hinner :
      0 < s ^ 5 + 12 * s ^ 4 + 49 * s ^ 3 + 87 * s ^ 2 + 148 * s - 108 := by
    have hterms : 0 ≤ 12 * s ^ 4 + 49 * s ^ 3 + 87 * s ^ 2 + 148 * s := by
      positivity
    nlinarith
  have hendpoint :
      0 < s * (s ^ 5 + 12 * s ^ 4 + 49 * s ^ 3 + 87 * s ^ 2 + 148 * s - 108) :=
    mul_pos hspos hinner
  refine ⟨hderiv_p, hminimum, ?_, ?_⟩
  · ring
  · calc
      s ^ 6 + 15 * s ^ 5 + 67 * s ^ 4 + 21 * s ^ 3 + 148 * s ^ 2 -
            108 * s - 12 * s * (s ^ 2 + 9 * s - 22) * (s ^ 2 / 4) +
              144 * (s ^ 2 / 4) ^ 2 =
          s * (s ^ 5 + 12 * s ^ 4 + 49 * s ^ 3 + 87 * s ^ 2 + 148 * s - 108) := by
        ring
      _ > 0 := hendpoint

end MathlibPlus.Algebra.Claim57427
