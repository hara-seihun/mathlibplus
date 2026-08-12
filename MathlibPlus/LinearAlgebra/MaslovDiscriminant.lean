import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra

/-- Claim 17593: the determinant of the displayed two-by-two Maslov matrix is
`-a²b² / (a²b² + 4)`. -/
theorem maslov_discriminant_identity_claim17593 (a b : ℝ) :
    let d : ℝ := a ^ 2 * b ^ 2 + 4
    Matrix.det (fun i j : Fin 2 =>
      if i = 0 then
        if j = 0 then 2 * a * b ^ 2 / d
        else -a * b * (a * b + 2) / d
      else
        if j = 0 then -a * b * (a * b + 2) / d
        else 2 * a ^ 2 * b / d) =
      -a ^ 2 * b ^ 2 / d := by
  dsimp
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = 0 then
      if j = 0 then 2 * a * b ^ 2 / (a ^ 2 * b ^ 2 + 4)
      else -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4)
    else
      if j = 0 then -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4)
      else 2 * a ^ 2 * b / (a ^ 2 * b ^ 2 + 4)
  change M.det = _
  rw [Matrix.det_fin_two M]
  simp [M]
  field_simp
  ring

end MathlibPlus.LinearAlgebra
