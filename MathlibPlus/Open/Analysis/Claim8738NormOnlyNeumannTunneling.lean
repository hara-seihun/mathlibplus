import Mathlib

open scoped BigOperators RealInnerProductSpace

namespace MathlibPlus.Open.Analysis

/-- The Euclidean operator norm of a real square matrix. -/
noncomputable def claim8738MatrixTwoNorm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin H)‖

/-- The coordinate vector supported at one finite coordinate. -/
noncomputable def claim8738CoordinateVector {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

/-- Conversion of a finite coordinate function to Euclidean space. -/
noncomputable def claim8738EuclideanVectorOfFunction {n : ℕ}
    (v : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm v

/-- The Euclidean inner product on the finite coordinate space. -/
noncomputable def claim8738EuclideanInner {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ u v

/-- The coordinate form of the trailing tridiagonal-block hypothesis. -/
def claim8738IsTridiagonal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n,
    (i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) → H i j = 0

/-- The norm-only Neumann-series tunneling estimate for the trailing Jacobi block. -/
def claim8738NormOnlyNeumannTunnelingBound
    (N k m : ℕ) (hkm : k < m) (hmN : m < N)
    (H_k : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ)
    (x B₀ : ℝ) : Prop :=
  let d : ℕ := m - k - 1
  let e₀ : EuclideanSpace ℝ (Fin (N - k - 1)) :=
    claim8738CoordinateVector ⟨0, by omega⟩
  let e_d : EuclideanSpace ℝ (Fin (N - k - 1)) :=
    claim8738CoordinateVector ⟨d, by omega⟩
  claim8738IsTridiagonal H_k →
    claim8738MatrixTwoNorm H_k ≤ B₀ →
    B₀ < x →
      |claim8738EuclideanInner e_d
          (claim8738EuclideanVectorOfFunction
            (Matrix.mulVec
              ((x • (1 : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ) - H_k)⁻¹)
              e₀))| ≤
        (x - B₀)⁻¹ * (B₀ / x) ^ d

end MathlibPlus.Open.Analysis
