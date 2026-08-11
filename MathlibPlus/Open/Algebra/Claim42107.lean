import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 42107, with both coefficient rings stated explicitly. -/
def reciprocalLiftIrreducible_claim42107 : Prop :=
  let pZ : Polynomial ℤ :=
    Polynomial.X ^ 14 - Polynomial.X ^ 12 + Polynomial.X ^ 7 - Polynomial.X ^ 2 + 1
  let pQ : Polynomial ℚ :=
    Polynomial.X ^ 14 - Polynomial.X ^ 12 + Polynomial.X ^ 7 - Polynomial.X ^ 2 + 1
  Irreducible pZ ∧ Irreducible pQ

end MathlibPlus.Open.Algebra
