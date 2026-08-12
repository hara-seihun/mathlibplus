import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim49572

/-- A relation tensor killed by multiplication has exactly one of the two
branches: it is already zero before multiplication, or it is a nonzero element
of the multiplication kernel. -/
theorem tensorZero_multiplicationBoundary_dichotomy
    {X Y : Type*} [Zero X] [Zero Y]
    (μ : X → Y) (T : X) (hμ : μ T = 0) :
    Xor (T = 0) (T ≠ 0 ∧ μ T = 0) := by
  by_cases hT : T = 0
  · left
    constructor
    · exact hT
    · intro h
      exact h.1 hT
  · right
    constructor
    · exact ⟨hT, hμ⟩
    · exact hT

end MathlibPlus.LinearAlgebra.Claim49572
