import Mathlib

namespace MathlibPlus.Open.Analysis.Claim4478

/-- The arithmetic function u_x, including the zero convention. -/
noncomputable def unitPhase (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    Complex.exp (Complex.I * (x : ℂ) * Real.log (n : ℝ))

/-- Multiplicativity for the arithmetic-function convention used here. -/
def IsMultiplicativeArithmeticFunction (f : ℕ → ℂ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧
    ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n

/-- Packaging u_x as an arithmetic function is multiplicative. -/
def multiplicativeArithmeticUnitPhase_claim4478 (x : ℝ) : Prop :=
  IsMultiplicativeArithmeticFunction (unitPhase x)

end MathlibPlus.Open.Analysis.Claim4478
