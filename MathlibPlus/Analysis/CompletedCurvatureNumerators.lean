import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11370

/-- The exact pole-free numerator identities from claim 11370.  The source's
`F` is represented by an arbitrary nonzero complex value together with its
first two jet values; the two margins are expanded in the statement, so no
undefined margin convention is hidden. -/
theorem completedCurvatureNumerators
    (F F' F'' : ℂ) (κ₆ : ℝ) (hF : F ≠ 0) :
    let P : ℝ := Complex.normSq F
    let H : ℝ := (F'' * star F).re - κ₆ * P
    let j : ℝ := (F' * star F).im
    let x : ℝ := (F' * star F).re
    let A₆ : ℝ := (F'' / F).re - κ₆ + ((F' / F).im) ^ 2
    let K₆ : ℝ :=
      (Complex.normSq F' + (F'' * star F).re) / P - κ₆
    P ^ 2 * A₆ = P * H + j ^ 2 ∧
      P ^ 2 * K₆ = P * H + j ^ 2 + x ^ 2 ∧
      P ^ 2 * K₆ = P ^ 2 * A₆ + x ^ 2 := by
  dsimp
  have hP : 0 < Complex.normSq F := Complex.normSq_pos.mpr hF
  have hP0 : Complex.normSq F ≠ 0 := ne_of_gt hP
  constructor
  · rw [Complex.div_re, Complex.div_im]
    field_simp [hP0]
    simp [Complex.normSq, Complex.mul_re]
    ring
  · constructor
    · field_simp [hP0]
      simp [Complex.normSq, Complex.mul_re]
      ring
    · rw [Complex.div_re, Complex.div_im]
      field_simp [hP0]
      simp [Complex.normSq, Complex.mul_re]
      ring

end MathlibPlus.Analysis.Claim11370
