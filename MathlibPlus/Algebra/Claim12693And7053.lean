import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- Claim 12693: the two roots of the reciprocal characteristic polynomial
`X^2 + 7 X + 9` have product 9 but unequal absolute values. -/
theorem claim12693_reciprocalRoots :
    let s : ℝ := Real.sqrt 13
    let rPlus : ℝ := (-7 + s) / 2
    let rMinus : ℝ := (-7 - s) / 2
    rPlus * rMinus = 9 ∧ |rPlus| ≠ |rMinus| ∧ rPlus ≠ -3 ∧ rMinus ≠ -3 := by
  dsimp
  have hs2 : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
    exact this
  have hs0 : 0 ≤ Real.sqrt (13 : ℝ) := Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt (13 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs7 : Real.sqrt (13 : ℝ) < 7 := by
    nlinarith
  have hpneg : (-7 + Real.sqrt (13 : ℝ)) / 2 < 0 := by
    linarith
  have hmneg : (-7 - Real.sqrt (13 : ℝ)) / 2 < 0 := by
    linarith
  constructor
  · nlinarith
  constructor
  · rw [abs_of_neg hpneg, abs_of_neg hmneg]
    nlinarith
  constructor <;> nlinarith

/-- Claim 7053: the invariant symmetric metrics for the displayed companion
matrix form the stated one-parameter family. -/
theorem claim7053_invariantMetric
    (a b c : ℝ)
    (hInv :
      (Matrix.transpose (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ)) *
          (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) *
          (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ) =
        9 • (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ)) :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
    let z : ℝ := 9 * a
    P = z • (!![(1 / 9 : ℝ), -7 / 18; -7 / 18, 1] :
      Matrix (Fin 2) (Fin 2) ℝ) ∧
      Matrix.det P = -13 * z ^ 2 / 324 := by
  dsimp
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] at h00 h01 h11
  have hc : c = 9 * a := by linarith [h00]
  have hb : b = -7 * a / 2 := by linarith [h01, hc]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, hb, hc] <;> ring
  · rw [Matrix.det_fin_two]
    simp [Matrix.smul_apply, hb, hc]
    ring

/-- The invariant family in Claim 7053 cannot contain a positive-definite
nonzero metric; its determinant is strictly negative away from the zero member. -/
theorem claim7053_noPositiveInvariantMetric
    (a b c : ℝ)
    (hInv :
      (Matrix.transpose (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ)) *
          (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) *
          (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℝ) =
        9 • (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ))
    (hpos : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    False := by
  have hform := claim7053_invariantMetric a b c hInv
  have hdetpos : 0 < Matrix.det (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) :=
    hpos.det_pos
  rw [hform.2] at hdetpos
  by_cases hz : 9 * a = 0
  · simp [hz] at hdetpos
  · have hzsq : 0 < (9 * a) ^ 2 := sq_pos_of_ne_zero hz
    nlinarith

end MathlibPlus.Algebra
