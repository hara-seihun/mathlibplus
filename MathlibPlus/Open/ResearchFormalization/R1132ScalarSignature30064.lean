import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1132ScalarSignature30064

noncomputable section

abbrev C7 := ZMod 7

/-- The offset derivative of the scalar normalized label `t ↦ a t`. -/
def scalarOffsetSignature (a : C7ˣ) (v : C7) : C7 → C7 :=
  fun w => (a : C7) * (v + 2 * w) - (a : C7) * v

/-- Claim 30064: every one of the six scalar normalized label maps has an
offset-independent signature on all seven offsets. -/
def claim30064 : Prop :=
  ∀ a : C7ˣ, ∀ v v' : C7,
    scalarOffsetSignature a v = scalarOffsetSignature a v'

end

end MathlibPlus.Open.ResearchFormalization.R1132ScalarSignature30064
