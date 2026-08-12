import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring

namespace MathlibPlus.LinearAlgebra.Claim12827

/-- Claim 12827: the standard complex wedge on a two-dimensional space
scales by the determinant, and its squared norm scales by the squared norm
of that determinant.  `A.det ≠ 0` is the matrix representation of the
source's `A ∈ GL₂(ℂ)` hypothesis. -/
theorem wedgeScaling
    (A : Matrix (Fin 2) (Fin 2) ℂ) (_hA : A.det ≠ 0)
    (u v : Fin 2 → ℂ) :
    let ω : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ :=
      fun x y => x 0 * y 1 - x 1 * y 0
    let Au : Fin 2 → ℂ := A.mulVec u
    let Av : Fin 2 → ℂ := A.mulVec v
    ω Au Av = A.det * ω u v ∧
      ‖ω Au Av‖ ^ 2 = ‖A.det‖ ^ 2 * ‖ω u v‖ ^ 2 := by
  dsimp
  have hw :
      (A.mulVec u) 0 * (A.mulVec v) 1 -
          (A.mulVec u) 1 * (A.mulVec v) 0 =
        A.det * (u 0 * v 1 - u 1 * v 0) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  constructor
  · exact hw
  · rw [hw]
    rw [norm_mul]
    ring

end MathlibPlus.LinearAlgebra.Claim12827
