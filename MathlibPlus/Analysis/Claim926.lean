import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim926

/-- The exact decimal-to-rational coefficient and the cleared-denominator
identity for the derivative formula in the packet. -/
theorem exactCoefficientAndDerivativeNumerator :
    let η : ℝ := 0.024334
    let A : ℝ → ℝ := fun C => C - 7 * 720.73002
    let Fderiv : ℝ → ℝ → ℝ := fun C L =>
      1 / L + η / L ^ 4 - 3 * η / L ^ 5 + A C / L ^ 8 - 8 * C / L ^ 9
    let Q : ℝ → ℝ → ℝ := fun C L =>
      L ^ 8 + η * L ^ 5 - 3 * η * L ^ 4 + (A C) * L - 8 * C
    (6097.16044 : ℝ) = 152429011 / 25000 ∧
      ∀ (C L : ℝ), L ≠ 0 → L ^ 9 * Fderiv C L = Q C L := by
  dsimp
  constructor
  · norm_num
  · intro C L hL
    field_simp [hL]

end MathlibPlus.Analysis.Claim926
