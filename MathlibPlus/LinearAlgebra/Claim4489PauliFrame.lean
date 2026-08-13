import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The ordered real 2-by-2 Pauli frame in admitted claim 4489. -/
def pauliI_claim4489 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

def pauliX_claim4489 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def pauliIY_claim4489 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

def pauliZ_claim4489 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def orderedRealPauliFrame_claim4489 : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![pauliI_claim4489, pauliX_claim4489, pauliIY_claim4489, pauliZ_claim4489]

end MathlibPlus.LinearAlgebra
