import Mathlib

namespace MathlibPlus.Open.Algebra.Claim9559

/-- The quadratic quotient for `u^2 - 3u + 1` is a field and its generator
satisfies the reciprocal relation from the admitted claim. -/
def quadraticQuotientFieldAndUnitRelation : Prop :=
  let g : Polynomial ℚ := Polynomial.X ^ 2 - 3 * Polynomial.X + 1
  let K := AdjoinRoot g
  let u : K := AdjoinRoot.root g
  IsField K ∧
    u ^ 2 = (3 : K) * u - 1 ∧
    u * ((3 : K) - u) = 1

end MathlibPlus.Open.Algebra.Claim9559
