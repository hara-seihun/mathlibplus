-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MathlibPlus.Algebra.Claim13306

open Polynomial

private def firstSylvesterMatrix : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, -1, -9, -5, 6, 3, 0, 0, 0, 0, 0;
    0, 1, -1, -9, -5, 6, 3, 0, 0, 0, 0;
    0, 0, 1, -1, -9, -5, 6, 3, 0, 0, 0;
    0, 0, 0, 1, -1, -9, -5, 6, 3, 0, 0;
    0, 0, 0, 0, 1, -1, -9, -5, 6, 3, 0;
    0, 0, 0, 0, 0, 1, -1, -9, -5, 6, 3;
    1, 1, -8, -14, 0, 9, 3, 0, 0, 0, 0;
    0, 1, 1, -8, -14, 0, 9, 3, 0, 0, 0;
    0, 0, 1, 1, -8, -14, 0, 9, 3, 0, 0;
    0, 0, 0, 1, 1, -8, -14, 0, 9, 3, 0;
    0, 0, 0, 0, 1, 1, -8, -14, 0, 9, 3
  ]

private def secondSylvesterMatrix : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, -1, -9, -5, 4, 1, 0, 0, 0, 0, 0;
    0, 1, -1, -9, -5, 4, 1, 0, 0, 0, 0;
    0, 0, 1, -1, -9, -5, 4, 1, 0, 0, 0;
    0, 0, 0, 1, -1, -9, -5, 4, 1, 0, 0;
    0, 0, 0, 0, 1, -1, -9, -5, 4, 1, 0;
    0, 0, 0, 0, 0, 1, -1, -9, -5, 4, 1;
    1, 1, -8, -14, -1, 6, 1, 0, 0, 0, 0;
    0, 1, 1, -8, -14, -1, 6, 1, 0, 0, 0;
    0, 0, 1, 1, -8, -14, -1, 6, 1, 0, 0;
    0, 0, 0, 1, 1, -8, -14, -1, 6, 1, 0;
    0, 0, 0, 0, 1, 1, -8, -14, -1, 6, 1
  ]

private def firstLowerFactor : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 2, 3, 12, 43, 160, 1, 0, 0, 0, 0;
    0, 1, 2, 3, 12, 43, 80 / 293, 1, 0, 0, 0;
    0, 0, 1, 2, 3, 12, 43 / 586, -220 / 551, 1, 0, 0;
    0, 0, 0, 1, 2, 3, 6 / 293, 19 / 58, 0, 1, 0;
    0, 0, 0, 0, 1, 2, 3 / 586, -138 / 551, 7 / 4, -1 / 16, 1
  ]

private def firstUpperFactor : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, -1, -9, -5, 6, 3, 0, 0, 0, 0, 0;
    0, 1, -1, -9, -5, 6, 3, 0, 0, 0, 0;
    0, 0, 1, -1, -9, -5, 6, 3, 0, 0, 0;
    0, 0, 0, 1, -1, -9, -5, 6, 3, 0, 0;
    0, 0, 0, 0, 1, -1, -9, -5, 6, 3, 0;
    0, 0, 0, 0, 0, 1, -1, -9, -5, 6, 3;
    0, 0, 0, 0, 0, 0, 586, 1574, 506, -1089, -480;
    0, 0, 0, 0, 0, 0, 0, -1102 / 293, -1218 / 293, 978 / 293, 603 / 293;
    0, 0, 0, 0, 0, 0, 0, 0, 4 / 19, 267 / 1102, 24 / 551;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 6 / 29, 9 / 58;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3 / 32
  ]

private def secondLowerFactor : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 2, 3, 12, 44, 164, 1, 0, 0, 0, 0;
    0, 1, 2, 3, 12, 44, 164 / 607, 1, 0, 0, 0;
    0, 0, 1, 2, 3, 12, 44 / 607, -460 / 879, 1, 0, 0;
    0, 0, 0, 1, 2, 3, 12 / 607, 316 / 879, 40 / 79, 1, 0;
    0, 0, 0, 0, 1, 2, 3 / 607, -176 / 293, 241 / 79, 10 / 21, 1
  ]

private def secondUpperFactor : Matrix (Fin 11) (Fin 11) ℚ :=
  !![
    1, -1, -9, -5, 4, 1, 0, 0, 0, 0, 0;
    0, 1, -1, -9, -5, 4, 1, 0, 0, 0, 0;
    0, 0, 1, -1, -9, -5, 4, 1, 0, 0, 0;
    0, 0, 0, 1, -1, -9, -5, 4, 1, 0, 0;
    0, 0, 0, 0, 1, -1, -9, -5, 4, 1, 0;
    0, 0, 0, 0, 0, 1, -1, -9, -5, 4, 1;
    0, 0, 0, 0, 0, 0, 607, 1645, 632, -700, -164;
    0, 0, 0, 0, 0, 0, 0, -879 / 607, -1065 / 607, 684 / 607, 188 / 607;
    0, 0, 0, 0, 0, 0, 0, 0, 79 / 293, 97 / 293, 44 / 879;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 21 / 79, 25 / 237;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -13 / 63
  ]

private theorem firstSylvester_factorization :
    firstSylvesterMatrix = firstLowerFactor * firstUpperFactor := by
  native_decide

private theorem secondSylvester_factorization :
    secondSylvesterMatrix = secondLowerFactor * secondUpperFactor := by
  native_decide

private theorem firstLowerFactor_det :
    firstLowerFactor.det = 1 := by
  have triangular :
      firstLowerFactor.BlockTriangular OrderDual.toDual := by
    native_decide
  rw [Matrix.det_of_lowerTriangular firstLowerFactor triangular]
  native_decide

private theorem firstUpperFactor_det :
    firstUpperFactor.det = 9 := by
  have triangular :
      firstUpperFactor.BlockTriangular id := by
    native_decide
  rw [Matrix.det_of_upperTriangular triangular]
  native_decide

private theorem secondLowerFactor_det :
    secondLowerFactor.det = 1 := by
  have triangular :
      secondLowerFactor.BlockTriangular OrderDual.toDual := by
    native_decide
  rw [Matrix.det_of_lowerTriangular secondLowerFactor triangular]
  native_decide

private theorem secondUpperFactor_det :
    secondUpperFactor.det = 13 := by
  have triangular :
      secondUpperFactor.BlockTriangular id := by
    native_decide
  rw [Matrix.det_of_upperTriangular triangular]
  native_decide

private theorem firstSylvesterMatrix_det :
    firstSylvesterMatrix.det = 9 := by
  rw [firstSylvester_factorization, Matrix.det_mul,
    firstLowerFactor_det, firstUpperFactor_det]
  norm_num

private theorem secondSylvesterMatrix_det :
    secondSylvesterMatrix.det = 13 := by
  rw [secondSylvester_factorization, Matrix.det_mul,
    secondLowerFactor_det, secondUpperFactor_det]
  norm_num

/-- Exact arithmetic core of admitted claim 13306.  The two displayed
11-by-11 matrices are the fixed-degree Sylvester matrices for the two
auxiliary polynomial pairs in the source packet; their determinants are the
reported resultant values 9 and 13. -/
theorem auxiliaryPairResultants_claim13306 :
    firstSylvesterMatrix.det = 9 ∧ secondSylvesterMatrix.det = 13 := by
  exact ⟨firstSylvesterMatrix_det, secondSylvesterMatrix_det⟩

end MathlibPlus.Algebra.Claim13306
