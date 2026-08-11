import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4962

/-- The homogeneous lift `[1, γ(q)]` of a point on a `d`-coordinate curve. -/
def homogeneousCoordinate {Q : Type*} {d : ℕ}
    (γ : Q → Fin d → ℝ) (q : Q) : Fin (d + 1) → ℝ :=
  Fin.cases 1 (fun i => γ q i)

/-- The projective evaluation matrix whose columns are the homogeneous
coordinates at the selected points. -/
def projectiveEvaluationMatrix {Q : Type*} {d : ℕ}
    (γ : Q → Fin d → ℝ) (q : Fin (d + 1) → Q) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => homogeneousCoordinate γ (q j) i

/-- The first row of the projective evaluation matrix is constant one. -/
theorem projectiveEvaluationMatrix_zero_row {Q : Type*} {d : ℕ}
    (γ : Q → Fin d → ℝ) (q : Fin (d + 1) → Q) (j : Fin (d + 1)) :
    projectiveEvaluationMatrix γ q 0 j = 1 := by
  rfl

/-- Every successor row records the corresponding coordinate of the curve. -/
theorem projectiveEvaluationMatrix_succ_row {Q : Type*} {d : ℕ}
    (γ : Q → Fin d → ℝ) (q : Fin (d + 1) → Q) (i : Fin d) (j : Fin (d + 1)) :
    projectiveEvaluationMatrix γ q i.succ j = γ (q j) i := by
  rfl

end MathlibPlus.LinearAlgebra.Claim4962
