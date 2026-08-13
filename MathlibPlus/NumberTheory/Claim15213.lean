import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim15213

noncomputable section

/-- The Selberg recursion operator from admitted claim 15213.

The hypothesis `ha` records the source domain `a(1) = 0`; the operator itself
is the sum of the pointwise logarithmic term and the Dirichlet self-convolution.
-/
def selbergRecursion (a : ArithmeticFunction ℝ) (_ha : a 1 = 0) : ArithmeticFunction ℝ :=
  ⟨fun n => a n * Real.log n + (a * a) n, by simp⟩

/-- The arithmetic function `n ↦ (log n)^2` used in the second-order term. -/
noncomputable def logSq : ArithmeticFunction ℝ :=
  ⟨fun n => (Real.log n) ^ 2, by simp⟩

/-- The second logarithmic Möbius convolution from admitted claim 15213. -/
noncomputable def lambdaTwo : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * logSq

end

end MathlibPlus.NumberTheory.Claim15213
