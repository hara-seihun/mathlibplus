import MathlibPlus.LinearAlgebra.Claim4489PauliFrame

namespace MathlibPlus.LinearAlgebra.PauliAlignment

/-- Claim 4494: the two displayed alignment projectors are complementary
idempotents in the ordered real two-dimensional coefficient frame. -/
def alignmentProjectorAlgebra_claim4494 : Prop :=
  let I := pauliI_claim4489
  let Pplus : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  let Pminus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
  Pplus * Pplus = Pplus ∧
    Pminus * Pminus = Pminus ∧
    Pplus * Pminus = 0 ∧
    Pminus * Pplus = 0 ∧
    Pplus + Pminus = I

/-- Claim 4495: each displayed alignment projector has matrix trace one. -/
def alignmentProjectorTraces_claim4495 : Prop :=
  let Pplus : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  let Pminus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
  Matrix.trace Pplus = 1 ∧ Matrix.trace Pminus = 1

end MathlibPlus.LinearAlgebra.PauliAlignment
