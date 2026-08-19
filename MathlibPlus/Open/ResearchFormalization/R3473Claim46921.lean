import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3473Claim46921

open scoped BigOperators

private def quadraticForm {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : ℝ :=
  dotProduct x (M.mulVec x)

/-- Claim 46921: at every finite rank, strict feasibility of the real
symmetric affine pencil is equivalent to strict positivity of C on the
A-null cone. -/
def finiteDimensionalPencilSeparationCriterion_claim46921 : Prop :=
  ∀ (N : ℕ)
    (A C : Matrix (Fin N) (Fin N) ℝ),
    Matrix.IsSymm A →
    Matrix.IsSymm C →
    ((∃ tau : ℝ, Matrix.PosDef (C - tau • A)) ↔
      ∀ x : Fin N → ℝ,
        x ≠ 0 →
        quadraticForm A x = 0 →
        0 < quadraticForm C x)

end MathlibPlus.Open.ResearchFormalization.R3473Claim46921
