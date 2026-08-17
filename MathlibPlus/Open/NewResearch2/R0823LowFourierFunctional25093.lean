import MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness

namespace MathlibPlus.Open.NewResearch2.R0823LowFourierFunctional25093

open scoped BigOperators

noncomputable section

/-- The Euler operator `D = t d/dt` on rational polynomials. -/
def eulerOperator (f : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.X * Polynomial.derivative f

/-- An iterate of the Euler operator. -/
def eulerPower : ℕ → Polynomial ℚ → Polynomial ℚ
  | 0, f => f
  | k + 1, f => eulerOperator (eulerPower k f)

/-- The action of a coefficient polynomial at the Euler operator. -/
def polynomialEulerAction (P f : Polynomial ℚ) : Polynomial ℚ :=
  P.sum (fun k a => Polynomial.C a * eulerPower k f)

/-- The displayed binomial test polynomial. -/
def lowFourierTest (n r s : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ r * (1 - Polynomial.X) ^ s *
    (1 + Polynomial.X) ^
      (MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness.M n - 2 * r - s)

/-- Claim 25093: the low Fourier functional is the defining Euler-action
expression evaluated at `t = 1`. -/
def lowFourierFunctional (n r s : ℕ) (P : Polynomial ℚ) : ℚ :=
  Polynomial.eval (1 : ℚ) (polynomialEulerAction P (lowFourierTest n r s))

end

end MathlibPlus.Open.NewResearch2.R0823LowFourierFunctional25093
