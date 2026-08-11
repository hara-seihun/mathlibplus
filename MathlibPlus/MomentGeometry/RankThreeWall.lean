import Mathlib

/-!
# Rank-three completed Bezout wall

The exact rank-three completed-Bezout determinant and its affine highest-ratio wall
from admitted claims 361--362.
-/

namespace MathlibPlus.MomentGeometry

/-- The rank-three completed Bezout determinant for factorial-normalized moments
`h_j = m_j / (2j)!`, expanded from the six symmetric matrix entries. -/
noncomputable def completedBezoutDet3 (m₀ m₁ m₂ m₃ m₄ m₅ : ℝ) : ℝ :=
  let h₀ := m₀
  let h₁ := m₁ / 2
  let h₂ := m₂ / 24
  let h₃ := m₃ / 720
  let h₄ := m₄ / 40320
  let h₅ := m₅ / 3628800
  let c₀₀ := h₀ * h₁
  let c₀₁ := 2 * h₀ * h₂
  let c₀₂ := 3 * h₀ * h₃
  let c₁₁ := 3 * h₀ * h₃ + h₁ * h₂
  let c₁₂ := 4 * h₀ * h₄ + 2 * h₁ * h₃
  let c₂₂ := 5 * h₀ * h₅ + 3 * h₁ * h₄ + h₂ * h₃
  c₀₀ * c₁₁ * c₂₂ + 2 * c₀₁ * c₀₂ * c₁₂ - c₀₀ * c₁₂ ^ 2 -
    c₁₁ * c₀₂ ^ 2 - c₂₂ * c₀₁ ^ 2

/-- The rank-two orientation parameter `a`. -/
def rankTwoOrientation (ρ₁ ρ₂ : ℝ) : ℝ :=
  3 * ρ₁ * ρ₂ - 10 * ρ₁ + 15

/-- The part of the scaled rank-three determinant independent of `ρ₄`. -/
def rankThreeConstant (ρ₁ ρ₂ ρ₃ : ℝ) : ℝ :=
  -180 * ρ₁ ^ 2 * ρ₂ ^ 3 * ρ₃ ^ 2 +
    2520 * ρ₁ ^ 2 * ρ₂ ^ 2 * ρ₃ -
    2646 * ρ₁ ^ 2 * ρ₂ ^ 2 -
    2205 * ρ₁ * ρ₂ ^ 2 * ρ₃ -
    9450 * ρ₁ * ρ₂ * ρ₃ +
    26460 * ρ₁ * ρ₂ - 14700 * ρ₁ +
    14175 * ρ₂ * ρ₃ - 35280 * ρ₂ + 22050

/-- The exact highest-ratio wall in the positive rank-two chamber. -/
noncomputable def rankThreeHighestRatioWall (ρ₁ ρ₂ ρ₃ : ℝ) : ℝ :=
  -rankThreeConstant ρ₁ ρ₂ ρ₃ /
    (35 * ρ₁ * ρ₂ ^ 2 * ρ₃ ^ 2 * rankTwoOrientation ρ₁ ρ₂)

/-- Direct expansion of the rank-three determinant in consecutive moment ratios. -/
theorem completedBezoutDet3_affine_formula
    (m₀ m₁ m₂ m₃ m₄ m₅ : ℝ)
    (hm₀ : m₀ ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (hm₃ : m₃ ≠ 0) (hm₄ : m₄ ≠ 0) :
    let ρ₁ := m₀ * m₂ / m₁ ^ 2
    let ρ₂ := m₁ * m₃ / m₂ ^ 2
    let ρ₃ := m₂ * m₄ / m₃ ^ 2
    let ρ₄ := m₃ * m₅ / m₄ ^ 2
    36578304000 * completedBezoutDet3 m₀ m₁ m₂ m₃ m₄ m₅ =
      (m₁ ^ 9 / m₀ ^ 3) * ρ₁ ^ 4 * ρ₂ *
        (35 * ρ₁ * ρ₂ ^ 2 * ρ₃ ^ 2 * rankTwoOrientation ρ₁ ρ₂ * ρ₄ +
          rankThreeConstant ρ₁ ρ₂ ρ₃) := by
  dsimp [completedBezoutDet3, rankTwoOrientation, rankThreeConstant]
  field_simp
  ring

/-- In the positive-moment, positive rank-two chamber, the coefficient of `ρ₄` is
positive and the rank-three determinant is positive exactly above its affine wall. -/
theorem rankThreeDet_pos_iff_highestRatio_gt_wall
    (m₀ m₁ m₂ m₃ m₄ m₅ : ℝ)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hm₃ : 0 < m₃) (hm₄ : 0 < m₄) (_hm₅ : 0 < m₅)
    (ha : 0 < rankTwoOrientation (m₀ * m₂ / m₁ ^ 2) (m₁ * m₃ / m₂ ^ 2)) :
    let ρ₁ := m₀ * m₂ / m₁ ^ 2
    let ρ₂ := m₁ * m₃ / m₂ ^ 2
    let ρ₃ := m₂ * m₄ / m₃ ^ 2
    let ρ₄ := m₃ * m₅ / m₄ ^ 2
    0 < 35 * ρ₁ * ρ₂ ^ 2 * ρ₃ ^ 2 * rankTwoOrientation ρ₁ ρ₂ ∧
      (0 < completedBezoutDet3 m₀ m₁ m₂ m₃ m₄ m₅ ↔
        rankThreeHighestRatioWall ρ₁ ρ₂ ρ₃ < ρ₄) := by
  dsimp only
  let ρ₁ := m₀ * m₂ / m₁ ^ 2
  let ρ₂ := m₁ * m₃ / m₂ ^ 2
  let ρ₃ := m₂ * m₄ / m₃ ^ 2
  let ρ₄ := m₃ * m₅ / m₄ ^ 2
  let a := rankTwoOrientation ρ₁ ρ₂
  let C := rankThreeConstant ρ₁ ρ₂ ρ₃
  let coeff := 35 * ρ₁ * ρ₂ ^ 2 * ρ₃ ^ 2 * a
  have hρ₁ : 0 < ρ₁ := by positivity
  have hρ₂ : 0 < ρ₂ := by positivity
  have hρ₃ : 0 < ρ₃ := by positivity
  have hcoeff : 0 < coeff := by
    dsimp [coeff, a, ρ₁, ρ₂] at *
    positivity
  refine ⟨hcoeff, ?_⟩
  have hpref : 0 < (m₁ ^ 9 / m₀ ^ 3) * ρ₁ ^ 4 * ρ₂ := by positivity
  have hscale : (0 : ℝ) < 36578304000 := by norm_num
  have hformula := completedBezoutDet3_affine_formula m₀ m₁ m₂ m₃ m₄ m₅
    hm₀.ne' hm₁.ne' hm₂.ne' hm₃.ne' hm₄.ne'
  dsimp only at hformula
  change 36578304000 * completedBezoutDet3 m₀ m₁ m₂ m₃ m₄ m₅ =
    (m₁ ^ 9 / m₀ ^ 3) * ρ₁ ^ 4 * ρ₂ * (coeff * ρ₄ + C) at hformula
  change 0 < completedBezoutDet3 m₀ m₁ m₂ m₃ m₄ m₅ ↔ -C / coeff < ρ₄
  constructor
  · intro hdet
    have hinner : 0 < coeff * ρ₄ + C := by
      have : 0 < (m₁ ^ 9 / m₀ ^ 3) * ρ₁ ^ 4 * ρ₂ * (coeff * ρ₄ + C) := by
        rw [← hformula]
        positivity
      exact pos_of_mul_pos_right this hpref.le
    rw [div_lt_iff₀ hcoeff]
    nlinarith
  · intro hwall
    rw [div_lt_iff₀ hcoeff] at hwall
    have hinner : 0 < coeff * ρ₄ + C := by nlinarith
    have : 0 < 36578304000 * completedBezoutDet3 m₀ m₁ m₂ m₃ m₄ m₅ := by
      rw [hformula]
      positivity
    exact pos_of_mul_pos_right this hscale.le

end MathlibPlus.MomentGeometry
