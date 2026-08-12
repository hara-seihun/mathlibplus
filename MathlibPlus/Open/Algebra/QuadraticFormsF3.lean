import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MathlibPlus.Open.Algebra.QuadraticFormsF3

/-- Claim 39680: classification of nonzero binary quadratic forms over `F₃`
under invertible linear changes of variables and nonzero scalar multiples. -/
def binaryQuadraticFormsF3Classification : Prop :=
  let Q : ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 :=
    fun a b c x y => a * x ^ 2 + b * x * y + c * y ^ 2
  let canonical : Fin 3 → ZMod 3 × ZMod 3 × ZMod 3 :=
    ![(1, 0, 0), (0, 1, 0), (1, 0, 1)]
  let equivalent (a b c : ZMod 3) (i : Fin 3) : Prop :=
    ∃ (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (s : ZMod 3),
      IsUnit M.det ∧ IsUnit s ∧
        ∀ x y : ZMod 3,
          Q a b c
              (M 0 0 * x + M 0 1 * y)
              (M 1 0 * x + M 1 1 * y) =
            s * Q (canonical i).1 (canonical i).2.1 (canonical i).2.2 x y
  ∀ a b c : ZMod 3,
    (a, b, c) ≠ (0, 0, 0) →
      ∃! i : Fin 3, equivalent a b c i

end MathlibPlus.Open.Algebra.QuadraticFormsF3
