import Mathlib

namespace MathlibPlus.Analysis.Claim6033

/-- Claim 6033: the unit-modulus rotated derivative block is exactly a
nonnegative square. -/
def rotatedDerivativeBlock : Prop :=
  ∀ (ω z : ℂ),
    ‖ω‖ = 1 →
      ‖z‖ ^ 2 + (ω ^ 2 * z ^ 2).re =
          2 * ((ω * z).re) ^ 2 ∧
        0 ≤ ‖z‖ ^ 2 + (ω ^ 2 * z ^ 2).re

end MathlibPlus.Analysis.Claim6033
