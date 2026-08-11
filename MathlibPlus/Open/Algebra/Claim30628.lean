import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 30628, expanding the source's `q`, `L`, and `g_d` in `ℚ[X]`. -/
def sexticFamilyIrreducible_claim30628 : Prop :=
  ∀ d : ℤ, 3 ≤ d →
    let x : Polynomial ℚ := Polynomial.X
    let q : Polynomial ℚ := x ^ 2 + x + 1
    let L : Polynomial ℚ := x + 1
    Irreducible (q ^ 3 + (Polynomial.C (d : ℚ) - L) * q - 1)

end MathlibPlus.Open.Algebra
