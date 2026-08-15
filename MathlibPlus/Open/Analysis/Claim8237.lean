import Mathlib
import MathlibPlus.Analysis.Claim8236

namespace MathlibPlus.Open.Analysis.Claim8237

noncomputable section

open MathlibPlus.Analysis.Claim8236

/-- The radial feature/tangent matrix from the admitted repair context. -/
def radialFeatureTangentMatrix (G : ℝ → ℝ) (A D J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ G A, D * A * deriv G A ;
      -D * A * deriv G A,
        deriv G A * J - D ^ 2 * (A * deriv G A + A ^ 2 * deriv (deriv G) A) ]

/-- Exact exterior determinant calculus. -/
def exactExteriorDeterminantCalculus : Prop :=
  ∀ (G : ℝ → ℝ) (A D J : ℝ),
    Matrix.det (radialFeatureTangentMatrix G A D J) =
      G A * deriv G A * J + D ^ 2 * radialTangentDefect G A

end

end MathlibPlus.Open.Analysis.Claim8237
