import Mathlib

/-!
# Variance form of the rank-two and rank-three boundary walls

This formalizes admitted claim 151 from packet `C-0010`.  The boundary
measure is `A δ₀ + B δ_z` with all three parameters positive.  The exact
radical wall is retained; the source's decimal is not asserted because no
error tolerance accompanies `≈`.
-/

namespace MathlibPlus.MomentGeometry

/-- Moments of the two-atom boundary measure `A δ₀ + B δ_z`. -/
noncomputable def twoAtomMoment (A B z : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then A + B else B * z ^ k

/-- The normalized variance `m₀m₂/m₁²` of the boundary measure. -/
noncomputable def twoAtomNormalizedVariance (A B z : ℝ) : ℝ :=
  twoAtomMoment A B z 0 * twoAtomMoment A B z 2 /
    twoAtomMoment A B z 1 ^ 2

/-- The positive root of the rank-three determinant polynomial in `A/B`. -/
noncomputable def rankThreeRatioWall : ℝ :=
  (-236 + 12 * Real.sqrt 4305) / 551

/-- The rank-three wall in normalized-variance coordinates. -/
noncomputable def rankThreeVarianceWall : ℝ :=
  (315 + 12 * Real.sqrt 4305) / 551

/-- The rank-two wall in normalized-variance coordinates. -/
noncomputable def rankTwoVarianceWall : ℝ := 15 / 7

/-- The exact rank-two completed-Bezout determinant on the boundary face. -/
def rankTwoBoundaryDet (A B z : ℝ) : ℝ :=
  -(B ^ 2 * z ^ 4) * (7 * A - 8 * B)

/-- The exact rank-three completed-Bezout determinant on the boundary face. -/
def rankThreeBoundaryDet (A B z : ℝ) : ℝ :=
  -(B ^ 3 * z ^ 9 * (A + B)) *
    (551 * A ^ 2 + 472 * A * B - 1024 * B ^ 2)

/-- For the nondegenerate two-atom measure, its moment definition of normalized
variance is exactly `1 + A/B`. -/
theorem twoAtomNormalizedVariance_eq
    (A B z : ℝ) (hB : 0 < B) (hz : 0 < z) :
    twoAtomNormalizedVariance A B z = 1 + A / B := by
  simp [twoAtomNormalizedVariance, twoAtomMoment]
  field_simp [ne_of_gt hB, ne_of_gt hz]
  ring

/-- The exact radical is the positive root of the rank-three ratio polynomial. -/
theorem rankThreeRatioWall_isRoot :
    551 * rankThreeRatioWall ^ 2 + 472 * rankThreeRatioWall - 1024 = 0 := by
  have hsqrt : (Real.sqrt 4305) ^ 2 = (4305 : ℝ) := by norm_num
  rw [rankThreeRatioWall]
  field_simp
  nlinarith

/-- Conversion of the rank-three ratio wall to normalized-variance coordinates. -/
theorem rankThreeVarianceWall_eq_one_add_ratioWall :
    rankThreeVarianceWall = 1 + rankThreeRatioWall := by
  rw [rankThreeVarianceWall, rankThreeRatioWall]
  ring

/-- Conversion of the rank-two ratio wall to normalized-variance coordinates. -/
theorem rankTwoVarianceWall_eq_one_add_eightSevenths :
    rankTwoVarianceWall = 1 + (8 / 7 : ℝ) := by
  norm_num [rankTwoVarianceWall]

/-- Positivity of the exact rank-two determinant is precisely the ratio bound
`A/B < 8/7`. -/
theorem rankTwoBoundaryDet_pos_iff
    (A B z : ℝ) (hB : 0 < B) (hz : 0 < z) :
    0 < rankTwoBoundaryDet A B z ↔ A / B < 8 / 7 := by
  have hf : 0 < B ^ 2 * z ^ 4 := mul_pos (sq_pos_of_pos hB) (pow_pos hz 4)
  have hratio : A / B < (8 / 7 : ℝ) ↔ 7 * A - 8 * B < 0 := by
    rw [div_lt_iff₀ hB]
    constructor <;> intro h <;> nlinarith
  rw [hratio]
  have hnegf : -(B ^ 2 * z ^ 4) < 0 := neg_neg_of_pos hf
  constructor
  · intro hdet
    by_contra hp
    have hp' : 0 ≤ 7 * A - 8 * B := le_of_not_gt hp
    have : rankTwoBoundaryDet A B z ≤ 0 := by
      rw [rankTwoBoundaryDet]
      exact mul_nonpos_of_nonpos_of_nonneg hnegf.le hp'
    exact (not_lt_of_ge this) hdet
  · intro hp
    rw [rankTwoBoundaryDet]
    exact mul_pos_of_neg_of_neg hnegf hp

/-- Negativity of the exact rank-three determinant is precisely strict passage
through the positive radical wall. -/
theorem rankThreeBoundaryDet_neg_iff
    (A B z : ℝ) (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) :
    rankThreeBoundaryDet A B z < 0 ↔ rankThreeRatioWall < A / B := by
  let r : ℝ := A / B
  let p : ℝ := 551 * r ^ 2 + 472 * r - 1024
  have hr : 0 < r := div_pos hA hB
  have hroot := rankThreeRatioWall_isRoot
  have hsecond : 0 < 551 * r + 551 * rankThreeRatioWall + 472 := by
    have hsqrt : 0 ≤ Real.sqrt 4305 := Real.sqrt_nonneg _
    have hwall : 551 * rankThreeRatioWall + 472 = 236 + 12 * Real.sqrt 4305 := by
      rw [rankThreeRatioWall]
      ring
    nlinarith [hwall]
  have hfactor :
      p = (r - rankThreeRatioWall) *
        (551 * r + 551 * rankThreeRatioWall + 472) := by
    dsimp [p]
    nlinarith
  have hp_iff : 0 < p ↔ rankThreeRatioWall < r := by
    rw [hfactor]
    constructor
    · intro hp
      by_contra hnot
      have hleft : r - rankThreeRatioWall ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hprod :
          (r - rankThreeRatioWall) *
              (551 * r + 551 * rankThreeRatioWall + 472) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hleft hsecond.le
      exact (not_lt_of_ge hprod) hp
    · intro h
      exact mul_pos (sub_pos.mpr h) hsecond
  have hpoly :
      551 * A ^ 2 + 472 * A * B - 1024 * B ^ 2 = B ^ 2 * p := by
    dsimp [p, r]
    field_simp [ne_of_gt hB]
  have hfront : 0 < B ^ 3 * z ^ 9 * (A + B) := by positivity
  rw [rankThreeBoundaryDet, hpoly]
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hsign :
      -(B ^ 3 * z ^ 9 * (A + B)) * (B ^ 2 * p) < 0 ↔ 0 < p := by
    constructor
    · intro hneg
      by_contra hpnot
      have hpnonpos : p ≤ 0 := le_of_not_gt hpnot
      have hinner : B ^ 2 * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBsq.le hpnonpos
      have hnonneg :
          0 ≤ -(B ^ 3 * z ^ 9 * (A + B)) * (B ^ 2 * p) := by
        have hnegfront : -(B ^ 3 * z ^ 9 * (A + B)) < 0 := by
          exact neg_neg_of_pos hfront
        exact mul_nonneg_of_nonpos_of_nonpos hnegfront.le hinner
      exact (not_lt_of_ge hnonneg) hneg
    · intro hp
      have hinner : 0 < B ^ 2 * p := mul_pos hBsq hp
      have hnegfront : -(B ^ 3 * z ^ 9 * (A + B)) < 0 := by
        exact neg_neg_of_pos hfront
      exact mul_neg_of_neg_of_pos hnegfront hinner
  rw [hsign, hp_iff]

/-- On the positive two-atom boundary face, rank-two positivity together with
rank-three negativity is exactly the open variance chamber between the two
walls.  Strict inequalities exclude both zero-determinant endpoints. -/
theorem varianceBoundaryWalls
    (A B z : ℝ) (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) :
    (0 < rankTwoBoundaryDet A B z ∧ rankThreeBoundaryDet A B z < 0) ↔
      rankThreeVarianceWall < twoAtomNormalizedVariance A B z ∧
        twoAtomNormalizedVariance A B z < rankTwoVarianceWall := by
  rw [rankTwoBoundaryDet_pos_iff A B z hB hz,
    rankThreeBoundaryDet_neg_iff A B z hA hB hz,
    twoAtomNormalizedVariance_eq A B z hB hz,
    rankThreeVarianceWall_eq_one_add_ratioWall,
    rankTwoVarianceWall_eq_one_add_eightSevenths]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end MathlibPlus.MomentGeometry
