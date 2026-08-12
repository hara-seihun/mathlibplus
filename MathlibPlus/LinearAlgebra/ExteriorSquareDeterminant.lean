import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

/--
Claim 19165 (R-0246): in coordinates for the basis `(e,o)`, the tensor square
of a two-dimensional operator sends `e ⊗ o - o ⊗ e` to its determinant times
that generator.  The coordinate identity is stated over an arbitrary
commutative ring, so no positivity or nonvanishing hypothesis is introduced.
-/
theorem tensorSquare_exteriorGenerator {R : Type*} [CommRing R]
    (B : Matrix (Fin 2) (Fin 2) R) :
    let ω : Fin 2 → Fin 2 → R := fun i j =>
      if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
    let tensorApply : (Fin 2 → Fin 2 → R) → (Fin 2 → Fin 2 → R) :=
      fun X i j => ∑ k, ∑ l, B i k * B j l * X k l
    tensorApply ω = fun i j => Matrix.det B * ω i j := by
  dsimp
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

end MathlibPlus.LinearAlgebra
