import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim13558

/-- The reciprocal diagonal block has no positive-definite conformal form. -/
def noPositiveConformalForm : Prop :=
  ¬ ∃ (G : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
    G.PosDef ∧
      (let U : Matrix (Fin 2) (Fin 2) ℝ :=
        !![(2 : ℝ), 0; 0, (1 / 2 : ℝ)]
       U.transpose * G * U = c • G)

end MathlibPlus.Open.LinearAlgebra.Claim13558
