import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The vertex/edge/nonedge Gegenbauer Gram matrix has the indicated inner-product entries. -/
def vertexEdgeNonedgeGegenbauerGramMatrix
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gV gE gN : E) (M_t : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  let g : Fin 3 → E := ![gV, gE, gN]
  M_t = fun A B => inner ℝ (g A) (g B)

end MathlibPlus.Open.Analysis
