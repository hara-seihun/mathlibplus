import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0261

abbrev ChannelVector := Fin 2 → ℂ
abbrev ChannelMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The real quadratic form of a complex channel matrix. -/
def hermitianQuadraticForm (A : ChannelMatrix) (v : ChannelVector) : ℝ :=
  (∑ i : Fin 2, star (v i) * (A.mulVec v) i).re

/-- Strict positivity of the quadratic form on a complex subspace. -/
def positiveOnSubspace (A : ChannelMatrix)
    (W : Submodule ℂ ChannelVector) : Prop :=
  ∀ v : ChannelVector, v ∈ W → v ≠ 0 → 0 < hermitianQuadraticForm A v

/-- Strict negativity of the quadratic form on a complex subspace. -/
def negativeOnSubspace (A : ChannelMatrix)
    (W : Submodule ℂ ChannelVector) : Prop :=
  ∀ v : ChannelVector, v ∈ W → v ≠ 0 → hermitianQuadraticForm A v < 0

/-- The dimensions realized by positive definite subspaces of the form. -/
def positiveInertia (A : ChannelMatrix) : Set ℕ :=
  {d | ∃ W : Submodule ℂ ChannelVector,
    Module.finrank ℂ W = d ∧ positiveOnSubspace A W}

/-- The dimensions realized by negative definite subspaces of the form. -/
def negativeInertia (A : ChannelMatrix) : Set ℕ :=
  {d | ∃ W : Submodule ℂ ChannelVector,
    Module.finrank ℂ W = d ∧ negativeOnSubspace A W}

/-- Hermitian inertia, represented by the positive and negative definite
subspace dimensions. -/
def hermitianInertia (A : ChannelMatrix) : Set ℕ × Set ℕ :=
  (positiveInertia A, negativeInertia A)

/-- A negative real eigenvalue exists in the two-channel matrix. -/
def hasNegativeEigenvalue (A : ChannelMatrix) : Prop :=
  ∃ eigenvalue : ℝ, eigenvalue < 0 ∧ ∃ v : ChannelVector, v ≠ 0 ∧
    A.mulVec v = (eigenvalue : ℂ) • v

/-- The determinant is a negative real number. -/
def hasNegativeRealDeterminant (A : ChannelMatrix) : Prop :=
  (Matrix.det A).im = 0 ∧ (Matrix.det A).re < 0

/-- Claim 15063: a constant invertible channel recombination is a Hermitian
congruence, so it preserves inertia and the negative central signature. -/
def claim_15063 : Prop :=
  ∀ (K P : ChannelMatrix),
    Matrix.IsHermitian K →
    IsUnit (Matrix.det P) →
    let K' := P.conjTranspose * K * P
    Matrix.IsHermitian K' ∧
      hermitianInertia K' = hermitianInertia K ∧
      Matrix.det K' =
        (Complex.normSq (Matrix.det P) : ℂ) * Matrix.det K ∧
      (hasNegativeEigenvalue K' ↔ hasNegativeEigenvalue K) ∧
      (hasNegativeRealDeterminant K' ↔ hasNegativeRealDeterminant K)

end MathlibPlus.Open.ResearchFormalization.O0261
