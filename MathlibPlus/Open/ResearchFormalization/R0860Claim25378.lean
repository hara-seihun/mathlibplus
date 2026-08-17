import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0860Claim25378

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The finite bivariate beta-weighted split on the actual nested polynomial
    carrier `Polynomial (Polynomial ℚ)`. -/
private noncomputable def betaSplit
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  ∑ a ∈ P.support, ∑ b ∈ (P.coeff a).support,
    Polynomial.monomial (a + b + 1)
      ((P.coeff a).coeff b * (Nat.factorial a : ℚ) *
        (Nat.factorial b : ℚ) /
          (Nat.factorial (a + b + 1) : ℚ))

private def bivariateMonomial (a b : ℕ) : Polynomial (Polynomial ℚ) :=
  Polynomial.monomial a (Polynomial.X ^ b)

/-- Claim 25378: the concrete factorial-conjugated split sends every
    bivariate monomial to the displayed beta-weighted output monomial. -/
def claim25378_betaWeightedFactorialSplit : Prop :=
  ∀ a b : ℕ,
    betaSplit (bivariateMonomial a b) =
      Polynomial.monomial (a + b + 1)
        ((Nat.factorial a : ℚ) * (Nat.factorial b : ℚ) /
          (Nat.factorial (a + b + 1) : ℚ))

end

end MathlibPlus.Open.ResearchFormalization.R0860Claim25378
