import Mathlib

namespace MathlibPlus.Combinatorics.Claim10448

/-- Claim 10448.  The polynomial `(1 + 2T + 2T²) / 5` is represented over
`ℂ` by its literal coefficients, and `2^(-1/2)` by `1 / √2`. -/
theorem codingPurity :
    ∀ z : ℂ,
      Polynomial.eval z
        (Polynomial.C (1 / 5 : ℂ) + Polynomial.C (2 / 5 : ℂ) * Polynomial.X +
          Polynomial.C (2 / 5 : ℂ) * Polynomial.X ^ 2) = 0 →
      ‖z‖ = 1 / Real.sqrt 2 := by
  intro z hz
  let r₁ : ℂ := (-1 + Complex.I) / 2
  let r₂ : ℂ := (-1 - Complex.I) / 2
  let p : Polynomial ℂ :=
    Polynomial.C (1 / 5 : ℂ) + Polynomial.C (2 / 5 : ℂ) * Polynomial.X +
      Polynomial.C (2 / 5 : ℂ) * Polynomial.X ^ 2
  have hz' : Polynomial.eval z p = 0 := by simpa [p] using hz
  have hzscalar : (2 / 5 : ℂ) * (z - r₁) * (z - r₂) = 0 := by
    calc
      (2 / 5 : ℂ) * (z - r₁) * (z - r₂) = Polynomial.eval z p := by
        simp [p, r₁, r₂]
        ring_nf
        norm_num
        ring
      _ = 0 := hz'
  have hc : (2 / 5 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hzscalar with hzero | hzero
  · rcases mul_eq_zero.mp hzero with hzero | hzero
    · exact (hc hzero).elim
    · have : z = r₁ := sub_eq_zero.mp hzero
      subst z
      dsimp [r₁]
      rw [Complex.norm_div, Complex.norm_def]
      norm_num [Complex.normSq_apply]
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · have : z = r₂ := sub_eq_zero.mp hzero
    subst z
    dsimp [r₂]
    rw [Complex.norm_div, Complex.norm_def]
    norm_num [Complex.normSq_apply]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end MathlibPlus.Combinatorics.Claim10448
