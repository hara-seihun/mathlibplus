import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped RealInnerProductSpace

/-- Norm-only Neumann tunneling bound. -/
def normOnlyNeumannTunnelingBound : Prop :=
  ∀ (N k m : ℕ)
    (Hk : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ)
    (B₀ x : ℝ),
    k < m →
    m < N →
    ∀ (i₀ id : Fin (N - k - 1)),
    i₀.val = 0 →
    id.val = m - k - 1 →
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Hk)‖ ≤ B₀ →
    B₀ < x →
    (∀ j : ℕ, j < m - k - 1 →
      inner ℝ ((EuclideanSpace.basisFun (Fin (N - k - 1)) ℝ) id)
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Hk ^ j))
          ((EuclideanSpace.basisFun (Fin (N - k - 1)) ℝ) i₀)) = 0) →
    |inner ℝ ((EuclideanSpace.basisFun (Fin (N - k - 1)) ℝ) id)
      (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin ((x • (1 : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ) - Hk)⁻¹))
        ((EuclideanSpace.basisFun (Fin (N - k - 1)) ℝ) i₀))|
      ≤ (x - B₀)⁻¹ * (B₀ / x) ^ (m - k - 1)

end MathlibPlus.Open.Analysis
