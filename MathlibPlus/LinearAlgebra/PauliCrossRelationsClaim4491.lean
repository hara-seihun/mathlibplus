import MathlibPlus.LinearAlgebra.Claim4489PauliFrame

namespace MathlibPlus.LinearAlgebra.PauliSquares

/-- Claim 4491: the ordered real Pauli frame has the two displayed cross
relations, and the cross factors anticommute. -/
def pauliCrossRelations_claim4491 : Prop :=
  let X := pauliX_claim4489
  let iY := pauliIY_claim4489
  let Z := pauliZ_claim4489
  X * iY = -Z ∧
    iY * X = Z ∧
    X * iY = -(iY * X)

end MathlibPlus.LinearAlgebra.PauliSquares
