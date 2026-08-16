import Mathlib

namespace MathlibPlus.Open.Algebra.Lehmer

def firstAuxiliaryPair : Prop :=
  let ℓ : Polynomial ℤ :=
    Polynomial.X ^ 5 + Polynomial.X ^ 4 - 5 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3
  let c₁ : Polynomial ℤ := Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 - Polynomial.X
  let q₁ : Polynomial ℤ := ℓ - 2 * c₁
  let r₁ : Polynomial ℤ := (Polynomial.X + 1) * q₁ + Polynomial.X * c₁
  q₁ = Polynomial.X ^ 5 - Polynomial.X ^ 4 - 9 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 6 * Polynomial.X + 3 ∧
    r₁ = Polynomial.X ^ 6 + Polynomial.X ^ 5 - 8 * Polynomial.X ^ 4 -
      14 * Polynomial.X ^ 3 + 9 * Polynomial.X + 3

end MathlibPlus.Open.Algebra.Lehmer
