import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8644

noncomputable def K (a x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a⁻¹, -x / (2 * a); -x / (2 * a), a]

/-- Determinant and positive-definiteness characterization of the exact quadratic-form matrix. -/
def determinant_and_elliptic_positivity_claim8644 : Prop :=
  ∀ (a x : ℝ),
    0 < a →
      Matrix.det (K a x) = 1 - x ^ 2 / (4 * a ^ 2) ∧
        (Matrix.PosDef (K a x) ↔ |x| < 2 * a)

end MathlibPlus.Open.Analysis.Claim8644
