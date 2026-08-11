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

end MathlibPlus.Algebra
