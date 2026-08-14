import Mathlib

namespace MathlibPlus.Open.Research

/-- A finite completed shift packet is balanced exactly when its total
exponent and first shift moment both vanish. -/
def balancedCompletedShiftPacket {ι : Type*} [Fintype ι]
    (exponent shift : ι → ℝ) : Prop :=
  (∑ j, exponent j = 0) ∧ (∑ j, exponent j * shift j = 0)

end MathlibPlus.Open.Research
