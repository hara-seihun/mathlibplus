import MathlibPlus.Basic

/-!
# The `2+2+2` quadratic norm identity

Claim 25054 is an exact polynomial identity over `ℝ`; no positivity or
nondegeneracy hypotheses occur in the stated claim.
-/

namespace MathlibPlus.Algebra

/-- Substituting `b = a + u` and `c = a + v` gives the stated negative quadratic
form and its completed-square expression. -/
theorem quadratic_norm_identity (a u v : ℝ) :
    let b := a + u
    let c := a + v
    (-a ^ 2 + a * b + a * c - b ^ 2 + b * c - c ^ 2 =
        -u ^ 2 + u * v - v ^ 2) ∧
      (-u ^ 2 + u * v - v ^ 2 =
        -(u - v / 2) ^ 2 - (3 / 4) * v ^ 2) := by
  dsimp
  constructor <;> ring

/-- The quadratic conjugation norm attached to `u^2 - 3u + 1 = 0`.

The quotient-field element in the source packet satisfies this relation; the
statement is written over an arbitrary commutative ring so that the rational
coefficient specialization is immediate. -/
theorem quadraticConjugationNorm_formula_claim9561
    {R : Type*} [CommRing R] (x y u : R)
    (hu : u ^ 2 - 3 * u + 1 = 0) :
    (x + y * u) * (x + y * (3 - u)) = x ^ 2 + 3 * x * y + y ^ 2 := by
  have hprod : u * (3 - u) = 1 := by
    calc
      u * (3 - u) = -(u ^ 2 - 3 * u + 1) + 1 := by ring
      _ = 1 := by rw [hu]; ring
  calc
    (x + y * u) * (x + y * (3 - u)) =
        x ^ 2 + 3 * x * y + y ^ 2 * (u * (3 - u)) := by ring
    _ = x ^ 2 + 3 * x * y + y ^ 2 := by rw [hprod]; ring

end MathlibPlus.Algebra
