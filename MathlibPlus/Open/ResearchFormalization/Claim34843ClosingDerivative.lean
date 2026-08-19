import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim34843

noncomputable section

/-- The leaf and order-two rooted boundary factors have different closing
first derivatives, so order alone does not determine the closing jet. -/
def orderOnlyClosingDerivativeIsFalse_claim34843 : Prop :=
  let v : Polynomial ℚ := Polynomial.X
  let z : Polynomial (Polynomial ℚ) := Polynomial.X
  let B_L : Polynomial (Polynomial ℚ) := Polynomial.C v + z
  let B_E : Polynomial (Polynomial ℚ) :=
    Polynomial.C v + Polynomial.C v * z + z ^ 2
  Polynomial.eval (1 - v) (Polynomial.derivative B_L) = 1 ∧
    Polynomial.eval (1 - v) (Polynomial.derivative B_E) = 2 - v ∧
    2 - v ≠ (2 : Polynomial ℚ)

end

end MathlibPlus.Open.ResearchFormalization.Claim34843
