import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Collision

open scoped BigOperators

noncomputable section

/-- Normalized moments `h_j = m_j/(2j)!`. -/
def normalizedMoment (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  m j / (Nat.factorial (2 * j) : ℝ)

/-- The normalized collision matrix. -/
def collisionMatrix (m : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
      ((i : ℕ) + (j : ℕ) + 1 - 2 * a : ℕ) *
        normalizedMoment m a *
        normalizedMoment m ((i : ℕ) + (j : ℕ) + 1 - a)

/-- The displayed normalized-moment and collision-matrix specification. -/
def normalizedMomentsAndCollisionMatrix : Prop :=
  ∀ (m : ℕ → ℝ) (N : ℕ) (i j : Fin N),
    collisionMatrix m N i j =
      ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        ((i : ℕ) + (j : ℕ) + 1 - 2 * a : ℕ) *
          normalizedMoment m a *
          normalizedMoment m ((i : ℕ) + (j : ℕ) + 1 - a)

/-- The two-variable collision kernel. -/
def twoVariableCollisionKernel (i j : ℕ) (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ a ∈ Finset.range (min i j + 1),
      ((i + j + 1 - 2 * a : ℕ) : ℝ) /
        ((Nat.factorial (2 * a) : ℝ) *
          (Nat.factorial (2 * (i + j + 1 - a)) : ℝ)) *
        (x ^ a * y ^ (i + j + 1 - a) +
          x ^ (i + j + 1 - a) * y ^ a)

/-- Moments of a one-atom measure at `t` with mass `m₀`. -/
def oneAtomMoments (m₀ t : ℝ) (j : ℕ) : ℝ :=
  m₀ * t ^ j

/-- The three one-atom determinant anchors. -/
def oneAtomDeterminantAnchors : Prop :=
  ∀ (m₀ t : ℝ),
    Matrix.det (collisionMatrix (oneAtomMoments m₀ t) 2) =
        m₀ ^ 4 * t ^ 4 / 180 ∧
      Matrix.det (collisionMatrix (oneAtomMoments m₀ t) 3) =
        m₀ ^ 6 * t ^ 9 / 35721000 ∧
      Matrix.det (collisionMatrix (oneAtomMoments m₀ t) 4) =
        m₀ ^ 8 * t ^ 16 / 100356600994650000

end

end MathlibPlus.Open.ResearchBatch.Collision
