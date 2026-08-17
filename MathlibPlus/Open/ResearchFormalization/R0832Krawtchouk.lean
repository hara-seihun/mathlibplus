import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0832Krawtchouk

noncomputable section

def eulerDerivative (P : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.X * P.derivative

def eulerPower : ℕ → Polynomial ℚ → Polynomial ℚ
  | 0, P => P
  | j + 1, P => eulerPower j (eulerDerivative P)

def polynomialOperator (P Q : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ P.support, P.coeff j • eulerPower j Q

/-- The exact admissible carrier for the Krawtchouk moment functional.  The
bound records the source's non-truncated exponent `M-2r-s`. -/
def krawtchoukMoment_claim27100
    (M r s : ℕ) (_h : 2 * r + s ≤ M) (P : Polynomial ℚ) : ℚ :=
  Polynomial.eval 1
    (polynomialOperator P
      (Polynomial.X ^ r * (1 - Polynomial.X) ^ s *
        (1 + Polynomial.X) ^ (M - 2 * r - s)))

end

end MathlibPlus.Open.ResearchFormalization.R0832Krawtchouk
