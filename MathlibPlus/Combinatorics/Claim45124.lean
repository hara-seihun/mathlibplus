import Mathlib

namespace MathlibPlus.Combinatorics.Claim45124

/-- Exact rational mass arithmetic in the displayed `K_{3,10}` witness.
The source-specific residual-edge and valid-cut APIs are deliberately not
reconstructed from the packet's prose; this theorem retains every displayed
mass and the resulting violation. -/
theorem exactMassViolationArithmetic_claim45124 :
    (30 : ℚ) * (1 / 2) = 15 ∧
    (0 : ℚ) + 1 = 1 ∧
    (30 : ℚ) * (1 / 2) - (0 + 1) = 14 := by
  norm_num

end MathlibPlus.Combinatorics.Claim45124
