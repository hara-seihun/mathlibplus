import Mathlib

namespace MathlibPlus.Analysis.Claim7404

open scoped BigOperators

/-- The normalized moment sequence `h_j = m_j/(2j)!` from admitted claim
7404.  The source supplies moments by an integral but does not fix a measure
in this claim, so the moment sequence is an explicit input here. -/
noncomputable def normalizedMoment (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  m j / (Nat.factorial (2 * j) : ℝ)

/-- The finite completed-Bezout entry displayed in claim 7404. -/
noncomputable def completedBezoutEntry (m : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (min i j + 1),
    ((i + j + 1 - 2 * a : ℕ) : ℝ) * normalizedMoment m a *
      normalizedMoment m (i + j + 1 - a)

/-- The rank-`N` matrix whose `(i,j)` entry is the completed-Bezout sum. -/
noncomputable def completedBezoutMatrix (m : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j =>
      completedBezoutEntry m i j

@[simp] theorem completedBezoutMatrix_apply
    (m : ℕ → ℝ) (N : ℕ) (i j : Fin N) :
    completedBezoutMatrix m N i j =
      ∑ a ∈ Finset.range (min i j + 1),
        ((i + j + 1 - 2 * a : ℕ) : ℝ) *
          normalizedMoment m a * normalizedMoment m (i + j + 1 - a) := by
  rfl

end MathlibPlus.Analysis.Claim7404
