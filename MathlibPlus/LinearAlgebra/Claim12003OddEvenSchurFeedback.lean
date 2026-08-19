import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12003

private def oddIndices12003 : Fin 2 → Fin 4 :=
  ![0, 2]

private def evenIndices12003 : Fin 2 → Fin 4 :=
  ![1, 3]

noncomputable def oddEvenSchurFeedback_claim12003
    (B : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  B.submatrix evenIndices12003 evenIndices12003 -
    B.submatrix evenIndices12003 oddIndices12003 *
      (1 + B.submatrix oddIndices12003 oddIndices12003)⁻¹ *
      B.submatrix oddIndices12003 evenIndices12003

end MathlibPlus.LinearAlgebra.Claim12003
