import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0190Claim12429

/-- Claim 12429: the prime-two von Mangoldt atom has the exact folded parity
coefficient shown in the packet. -/
def claim12429 : Prop :=
  ArithmeticFunction.vonMangoldt 2 = Real.log 2 ∧
    -2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 =
      -Real.sqrt 2 * Real.log 2

end MathlibPlus.Open.ResearchFormalization.O0190Claim12429
