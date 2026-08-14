import Mathlib

namespace MathlibPlus.Open.Algebra

open Polynomial

/-- The candidate polynomial from claim 58751. -/
noncomputable def candidateC : Polynomial ℤ :=
  X ^ 6 + 2 * X ^ 5 - X ^ 4 + 3 * X ^ 3 - 2 * X + 1

/-- The algebraic properties asserted for the candidate polynomial in claim 58751.

For an irreducible monic integer polynomial, being noncyclotomic is expressed by
not being any cyclotomic polynomial. -/
def candidatePolynomialProperties : Prop :=
  candidateC.Monic ∧
    Irreducible candidateC ∧
      ¬ ∃ n : ℕ, candidateC = cyclotomic n ℤ

end MathlibPlus.Open.Algebra
