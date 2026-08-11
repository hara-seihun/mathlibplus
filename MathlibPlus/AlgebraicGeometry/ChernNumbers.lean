import Mathlib.Tactic

namespace MathlibPlus.AlgebraicGeometry.ChernNumbers

/-- For the Chern pair `(c₁², c₂) = (2, 10)`, Noether's formula forces the
holomorphic Euler characteristic to be `1`.

The geometric input is represented exactly by the integer Noether equality
`12 * χ = c₁² + c₂`; the theorem isolates its numerical consequence. -/
theorem chernPairTwoTen_noetherEulerCharacteristic
    (χ : ℤ) (hNoether : 12 * χ = (2 : ℤ) + 10) : χ = 1 := by
  omega

/-- Both entries of the Chern pair `(2, 10)` are positive. -/
theorem chernPairTwoTen_positive : (0 : ℤ) < 2 ∧ (0 : ℤ) < 10 := by
  norm_num

/-- The Chern pair `(2, 10)` satisfies the displayed Noether geography
inequality, including the two numerical evaluations in the source claim. -/
theorem chernPairTwoTen_noetherInequality :
    5 * (2 : ℤ) = 10 ∧ (10 : ℤ) - 36 = -26 ∧ (10 : ℤ) - 36 ≤ 5 * 2 := by
  norm_num

/-- The Chern pair `(2, 10)` satisfies the Bogomolov--Miyaoka--Yau numerical
inequality, with right-hand side `30`. -/
theorem chernPairTwoTen_bogomolovMiyaokaYau :
    (2 : ℤ) ≤ 3 * 10 ∧ 3 * (10 : ℤ) = 30 := by
  norm_num

end MathlibPlus.AlgebraicGeometry.ChernNumbers
