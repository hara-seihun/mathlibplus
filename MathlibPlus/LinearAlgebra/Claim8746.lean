import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim8746

open scoped MatrixOrder

/-- The positive spectral excursion inequality for a self-adjoint real
matrix, retained as a proof-free source assertion. -/
def positive_excursion_decomposition : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) (hJ : IsSelfAdjoint J) (B : ℝ),
    J ≤ B • (1 : Matrix n n ℝ) +
      (J - B • (1 : Matrix n n ℝ))⁺

/-- The corresponding compression inequality for an orthogonal projection. -/
def compressed_positive_excursion_decomposition : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) (hJ : IsSelfAdjoint J) (B : ℝ)
    (Q : Matrix n n ℝ) (hQ : IsStarProjection Q),
    Q * J * Q ≤
      B • Q + Q * (J - B • (1 : Matrix n n ℝ))⁺ * Q

end MathlibPlus.LinearAlgebra.Claim8746
