import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

open scoped BigOperators

noncomputable section

open Classical

/-- Squared Euclidean length on the two-dimensional coordinate space. -/
def euclideanSquared (x : Fin 2 → ℝ) : ℝ :=
  ∑ k : Fin 2, x k ^ 2

/-- The residual matrix associated to finite circle columns and arbitrary rows. -/
def circleResidualMatrix (m : ℕ) (C : Finset (Fin 2 → ℝ))
    (q : Fin m → (Fin 2 → ℝ)) (rho : Fin m → ℝ) :
    Matrix (Fin m) {x // x ∈ C} ℝ :=
  fun i x => euclideanSquared (q i - (x : Fin 2 → ℝ)) - rho i

/-- Every residual matrix on a retained circle has real rank at most three. -/
def retainedCircleResidualRankThree : Prop :=
  ∀ (m : ℕ) (C : Finset (Fin 2 → ℝ)) (a : Fin 2 → ℝ) (R : ℝ)
    (q : Fin m → (Fin 2 → ℝ)) (rho : Fin m → ℝ),
    (∀ x : {x // x ∈ C},
      euclideanSquared ((x : Fin 2 → ℝ) - a) = R ^ 2) →
    Matrix.rank (circleResidualMatrix m C q rho) ≤ 3

end

end MathlibPlus.Open.LinearAlgebra
