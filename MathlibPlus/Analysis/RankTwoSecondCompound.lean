import Mathlib

namespace MathlibPlus.Analysis

/-- The exact rank-two second-compound formula from admitted claim 14040.
The variables `x₁,x₂,y₁,y₂` are the squared-age coordinates of the two
ordered node pairs; the identity itself is valid over all real coordinates
with distinct entries. -/
theorem rankTwoSecondCompoundFormula_claim14040
    (a b x₁ x₂ y₁ y₂ : ℝ)
    (hx : x₁ < x₂)
    (hy : y₁ < y₂) :
    let S : ℝ → ℝ → ℝ := fun x y =>
      a ^ 2 + (a * b / 6) * (x + y) +
        (b ^ 2 / 360) * (x ^ 2 + 16 * x * y + y ^ 2)
    let E : ℝ :=
      (S x₁ y₁ * S x₂ y₂ - S x₁ y₂ * S x₂ y₁) /
        ((x₂ - x₁) * (y₂ - y₁))
    E = -b ^ 2 / 129600 *
      (-2160 * a ^ 2 + 60 * a * b * (x₁ + x₂ + y₁ + y₂) +
        b ^ 2 * (16 * x₁ * x₂ + x₁ * y₁ + x₁ * y₂ +
          x₂ * y₁ + x₂ * y₂ + 16 * y₁ * y₂)) := by
  dsimp
  have hx0 : x₂ - x₁ ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hy0 : y₂ - y₁ ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  field_simp [hx0, hy0]
  ring

/-- The exact positive and negative numerical witnesses from admitted claim
14041, using the preceding rank-two secant polynomial and compound formula. -/
theorem rankTwoSecondCompoundWitnesses_claim14041 :
    let S : ℝ → ℝ → ℝ := fun x y =>
      (-1 / 12 : ℝ) ^ 2 + ((-1 / 12 : ℝ) / 6) * (x + y) +
        ((1 : ℝ) ^ 2 / 360) * (x ^ 2 + 16 * x * y + y ^ 2)
    let E : ℝ → ℝ → ℝ → ℝ → ℝ := fun x₁ x₂ y₁ y₂ =>
      (S x₁ y₁ * S x₂ y₂ - S x₁ y₂ * S x₂ y₁) /
        ((x₂ - x₁) * (y₂ - y₁))
    (E (1 / 100) (1 / 25) (1 / 100) (1 / 25) =
        154847 / 1296000000 ∧
      0 < E (1 / 100) (1 / 25) (1 / 100) (1 / 25)) ∧
    (E (1 / 100) 1 1 4 = -151 / 810000 ∧
      E (1 / 100) 1 1 4 < 0) := by
  norm_num

end MathlibPlus.Analysis
