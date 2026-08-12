import Mathlib

open scoped ENNReal

namespace MathlibPlus.Open.LinearAlgebra

/-- Registry node for admitted claim 18084 (R-0120): a real square matrix with
spectral radius strictly below one has positive `det (I + B)`.  The spectral
radius is Mathlib's `ℝ`-spectrum radius, valued in `ℝ≥0∞`; nonreal eigenvalues
are consequently handled by the real determinant rather than by an
extra choice of eigenvalue interface. -/
def spectralRadiusOnePlusDetPositive : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (B : Matrix n n ℝ),
    spectralRadius ℝ B < (1 : ℝ≥0∞) →
      0 < Matrix.det (1 + B)

end MathlibPlus.Open.LinearAlgebra
