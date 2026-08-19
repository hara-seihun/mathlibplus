import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0561TriangleNonadjacency

/-- Claim 22708: the three endpoint pairs of a signed triangle can all be
selected mutually nonadjacent exactly for odd total sign. -/
def triangleNonadjacencyCriterion_claim22708 : Prop :=
  ∀ s_ij s_ik s_jk : ZMod 2,
    ((∃ x_i x_j x_k : ZMod 2,
        x_i + x_j ≠ s_ij ∧
        x_i + x_k ≠ s_ik ∧
        x_j + x_k ≠ s_jk) ↔
      s_ij + s_ik + s_jk = 1)

end MathlibPlus.Open.ResearchFormalization.R0561TriangleNonadjacency
