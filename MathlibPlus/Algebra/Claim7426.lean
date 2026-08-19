import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MathlibPlus.Algebra.Claim7426

/-- The divided projective curvature used in Claim 7426. -/
def dividedProjectiveCurvature {K : Type*} [Field K]
    (x₁ x₂ x₃ y₁ y₂ y₃ : K) : K :=
  ((y₃ - y₂) / (x₃ - x₂) - (y₂ - y₁) / (x₂ - x₁)) / (x₃ - x₁)

/-- Proof-free registry assertion for Claim 7426's determinant identity, with
its source `q_i,t` notation represented by the displayed affine coordinates. -/
def dividedProjectiveCurvature_identity : Prop :=
  ∀ {K : Type*} [Field K]
    (x₁ x₂ x₃ y₁ y₂ y₃ : K),
    x₂ - x₁ ≠ 0 →
    x₃ - x₂ ≠ 0 →
    x₃ - x₁ ≠ 0 →
    Matrix.det
        (!![1, x₁, y₁; 1, x₂, y₂; 1, x₃, y₃] : Matrix (Fin 3) (Fin 3) K) =
      (x₂ - x₁) * (x₃ - x₂) * (x₃ - x₁) *
        dividedProjectiveCurvature x₁ x₂ x₃ y₁ y₂ y₃

end MathlibPlus.Algebra.Claim7426
