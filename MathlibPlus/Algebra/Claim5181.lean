import Mathlib

namespace MathlibPlus.Algebra.Claim5181

/--
Claim 5181.  The displayed triangular coordinate change and its inverse have
exact determinant factors `2` and `1/2`, and their matrix actions are the
stated coordinate formulas.
-/
theorem exactTriangularCoordinateChange_claim5181 :
    let F : Matrix (Fin 4) (Fin 4) ℚ :=
      !![1, 0, 0, 0;
         2, -1, 0, 0;
         4, -3, 2, 0;
         0, 1, 0, -1]
    let G : Matrix (Fin 4) (Fin 4) ℚ :=
      !![1, 0, 0, 0;
         2, -1, 0, 0;
         1, -(3 : ℚ) / 2, 1 / 2, 0;
         2, -1, 0, -1]
    Matrix.det F = 2 ∧ Matrix.det G = (1 : ℚ) / 2 ∧
      (∀ a d q m : ℚ,
        Matrix.mulVec F ![a, d, q, m] =
          ![a, 2 * a - d, 4 * a - 3 * d + 2 * q, d - m]) ∧
      (∀ a chi chi₂ kappa : ℚ,
        Matrix.mulVec G ![a, chi, chi₂, kappa] =
          ![a, 2 * a - chi, (chi₂ - 3 * chi + 2 * a) / 2,
            2 * a - chi - kappa]) := by
  dsimp
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro a d q m
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · intro a chi chi₂ kappa
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

end MathlibPlus.Algebra.Claim5181
