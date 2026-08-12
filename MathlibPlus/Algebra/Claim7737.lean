import Mathlib

namespace MathlibPlus.Algebra.Claim7737

/--
Swapping the plus and minus components fixes the even combination and negates
the odd combination.  The quotient by `2 * Complex.I` is the source's exact
normalization of the odd component.
-/
theorem parity_decomposition_under_reflection (zPlus zMinus : ℂ) :
    let zEven : ℂ := (zPlus + zMinus) / 2
    let zOdd : ℂ := (zPlus - zMinus) / (2 * Complex.I)
    (zMinus + zPlus) / 2 = zEven ∧
      (zMinus - zPlus) / (2 * Complex.I) = -zOdd := by
  dsimp
  constructor <;> ring

end MathlibPlus.Algebra.Claim7737
