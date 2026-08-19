import Mathlib

namespace MathlibPlus.AlgebraicGeometry.NoetherArithmeticClaims14634_14638_14648_14653

/-- Claim 14634: the displayed Noether relation and Chern-number values force
`chi = 1`; no surface-existence assertion is added. -/
theorem noetherEulerCharacteristic_claim14634
    (chi c1Sq c2 : ℤ)
    (hc1Sq : c1Sq = 9)
    (hc2 : c2 = 3)
    (hNoether : 12 * chi = c1Sq + c2) :
    chi = 1 := by
  omega

/-- Claim 14638: the displayed Noether relation and Chern-number values force
`chi = 2`; no surface-existence assertion is added. -/
theorem noetherEulerCharacteristic_claim14638
    (chi c1Sq c2 : ℤ)
    (hc1Sq : c1Sq = 1)
    (hc2 : c2 = 23)
    (hNoether : 12 * chi = c1Sq + c2) :
    chi = 2 := by
  omega

/-- Claim 14648: both entries of the displayed Chern pair are positive. -/
theorem positivityAdmissibility_claim14648 :
    (0 : ℤ) < 5 ∧ (0 : ℤ) < 19 := by
  norm_num

/-- Claim 14653: the displayed Noether-formula value is exactly `2`. -/
theorem noetherEulerValue_claim14653 :
    let chi : ℚ := (6 + 18) / 12
    chi = 2 := by
  norm_num

end MathlibPlus.AlgebraicGeometry.NoetherArithmeticClaims14634_14638_14648_14653
