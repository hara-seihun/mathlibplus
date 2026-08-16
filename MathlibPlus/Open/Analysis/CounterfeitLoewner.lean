import Mathlib

/-!
# Smallest matrix-order Loewner falsifier for the reciprocal counterfeit

This registry node records admitted claim 260 from source record `C-0016`.
It includes the global order-one positivity inherited from Record 12, the exact
order-two divided-difference matrix at the stated nodes, the closed determinant
formula and interval, and the diagonal congruence to the exponential kernel.
-/

namespace MathlibPlus.Open.Analysis.CounterfeitLoewner

/-- The reciprocal positive-Euler counterfeit passes every scalar test but fails at
matrix order two at `λ = (3/4, 1)`, with the stated exact determinant. -/
noncomputable def smallestOrderFalsifier : Prop :=
  let H : ℝ → ℝ := fun x =>
    2 * Real.log 9 * Real.sinh (Real.log 9 * Real.sqrt x) /
      (Real.sqrt x *
        (2 * Real.cosh (Real.log 9 * Real.sqrt x) + 7 / 3))
  let rates : Fin 2 → ℝ := fun i => if i = 0 then 3 / 4 else 1
  let x : Fin 2 → ℝ := fun i => rates i ^ 2
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = j then -deriv H (x i)
    else -(H (x i) - H (x j)) / (x i - x j)
  let Q : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    4 * rates i * rates j * M i j
  let E : ℝ → ℝ := fun ell =>
    4060287 * ell ^ 2 + 7368669 * Real.sqrt 3 * ell ^ 2
      - 26422368 * ell - 19399737 * Real.sqrt 3 * ell
      - 109677424 + 89664260 * Real.sqrt 3
  let ell : ℝ := Real.log 3
  (∀ y : ℝ, 0 < y → 0 < -deriv H y) ∧
    x 0 = 9 / 16 ∧ x 1 = 1 ∧
    0 < M 0 0 ∧ 0 < M 1 1 ∧
    Matrix.det M =
      512 * ell ^ 2 * E ell /
        (229249881 * (3 + 4 * Real.sqrt 3) ^ 2) ∧
    Matrix.det M < 0 ∧
    -(339195 : ℝ) / 1000000000 ≤ Matrix.det M ∧
    Matrix.det M ≤ -(339194 : ℝ) / 1000000000 ∧
    Matrix.det Q = 16 * x 0 * x 1 * Matrix.det M ∧
    Matrix.det Q < 0

end MathlibPlus.Open.Analysis.CounterfeitLoewner
