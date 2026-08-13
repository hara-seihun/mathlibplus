import Mathlib

namespace MathlibPlus.LinearAlgebra

open scoped Matrix
set_option maxHeartbeats 800000
noncomputable section

private def rankFourR : ℝ := Real.sqrt (3 / 2)

private def rankFourA : Matrix (Fin 2) (Fin 1) ℝ :=
  !![rankFourR; rankFourR]

private def rankFourB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 / 2, 1 / 2; 1 / 2, 3 / 2]

private def rankFourC : Matrix (Fin 1) (Fin 2) ℝ :=
  !![rankFourR, rankFourR]

private def rankFourU : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0;
     rankFourR, 0, 0, 0, 0, 0;
     rankFourR, 0, 0, 0, 0, 0;
     0, 3 / 2, 1 / 2, 0, 0, 0;
     0, 1 / 2, 3 / 2, 0, 0, 0;
     0, 0, 0, rankFourR, rankFourR, 0]

private def rankFourD : Matrix (Fin 6) (Fin 6) ℝ := rankFourU.transpose

private def rankFourH : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-3, 0, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 3]

private lemma rankFourR_sq : rankFourR * rankFourR = (3 / 2 : ℝ) := by
  dsimp [rankFourR]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]

private lemma rankFour_block_BtB :
    rankFourB.transpose * rankFourB =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + rankFourA * rankFourA.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourA, rankFourB, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, rankFourR_sq]
  all_goals ring

private lemma rankFour_block_BB_transpose :
    rankFourB * rankFourB.transpose =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + rankFourC.transpose * rankFourC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourB, rankFourC, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, rankFourR_sq]
  all_goals ring

private lemma rankFour_block_AtA :
    rankFourA.transpose * rankFourA =
      (!![3] : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourA, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, rankFourR_sq]

private lemma rankFour_block_CCt :
    rankFourC * rankFourC.transpose =
      (!![3] : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourC, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, rankFourR_sq]

private lemma rankFour_sl2_commutator :
    rankFourU * rankFourD - rankFourD * rankFourU = rankFourH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourU, rankFourD, rankFourH, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      rankFourR_sq]
  all_goals ring

private lemma rankFour_sl2_raise :
    rankFourH * rankFourU - rankFourU * rankFourH =
      (2 : ℝ) • rankFourU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourU, rankFourH, Matrix.mul_apply, Fin.sum_univ_succ,
      smul_eq_mul]
  all_goals ring

private lemma rankFour_sl2_lower :
    rankFourH * rankFourD - rankFourD * rankFourH =
      -(2 : ℝ) • rankFourD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankFourU, rankFourD, rankFourH, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      smul_eq_mul]
  all_goals ring

/--
The literal rank-block and commutator certificate from claim 26751.  The
source packet names an order-four edge-poset realization but does not specify
its basis ordering; this theorem therefore exposes the displayed blocks and
one explicit six-coordinate block realization directly.
-/
theorem positiveAdjointSl2Structure_claim26751 :
    (0 < rankFourR ∧ 0 < (1 / 2 : ℝ) ∧ 0 < (3 / 2 : ℝ)) ∧
      rankFourB.transpose * rankFourB =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          rankFourA * rankFourA.transpose ∧
      rankFourB * rankFourB.transpose =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          rankFourC.transpose * rankFourC ∧
      rankFourA.transpose * rankFourA =
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ) ∧
      rankFourC * rankFourC.transpose =
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ) ∧
      rankFourU * rankFourD - rankFourD * rankFourU = rankFourH ∧
      rankFourH * rankFourU - rankFourU * rankFourH =
        (2 : ℝ) • rankFourU ∧
      rankFourH * rankFourD - rankFourD * rankFourH =
        -(2 : ℝ) • rankFourD := by
  have hrpos : 0 < rankFourR := by
    dsimp [rankFourR]
    positivity
  exact ⟨⟨hrpos, by norm_num, by norm_num⟩,
    rankFour_block_BtB,
    rankFour_block_BB_transpose,
    rankFour_block_AtA,
    rankFour_block_CCt,
    rankFour_sl2_commutator,
    rankFour_sl2_raise,
    rankFour_sl2_lower⟩

end
end MathlibPlus.LinearAlgebra
