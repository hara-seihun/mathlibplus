import Mathlib

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.R4467S2

abbrev F₃ := ZMod 3
abbrev QuotientSpace := Fin 5 → F₃

private def q1223 : QuotientSpace → QuotientSpace := fun x =>
  ![x 0, x 1,
    x 2 + x 0 * (x 0 - 1),
    x 3 + (2 * x 0 - 1) * x 1,
    x 4 + x 1 ^ 2]

private def q4431 : QuotientSpace → QuotientSpace := fun x =>
  ![x 0 + x 1 * x 2, x 1, x 2, x 3, x 4]

/-- Claim 52384: the two fixed quotient permutations over `𝔽₃`. -/
def claim52384 : Prop :=
  Function.Bijective q1223 ∧ Function.Bijective q4431 ∧
    q1223 0 = 0 ∧ q4431 0 = 0

end MathlibPlus.Open.FormalizationBatch.R4467S2
