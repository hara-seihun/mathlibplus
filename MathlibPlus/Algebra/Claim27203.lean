import Mathlib

namespace MathlibPlus.Algebra.Claim27203

/-- The quartic and cubic characteristic-polynomial identities in claim 27203. -/
theorem quarticCharacteristicTransport {R : Type*} [CommRing R]
    (b m c d : R) :
    let e₁ := b + m + c + d
    let e₂ := b * m + b * c + b * d + m * c + m * d + c * d
    let e₃ := b * m * c + b * m * d + b * c * d + m * c * d
    let e₄ := b * m * c * d
    let X : Polynomial R := Polynomial.X
    let χ := X ^ 4 - Polynomial.C e₁ * X ^ 3 +
      Polynomial.C e₂ * X ^ 2 - Polynomial.C e₃ * X + Polynomial.C e₄
    let cPoly := X ^ 3 - Polynomial.C e₁ * X ^ 2 +
      Polynomial.C e₂ * X - Polynomial.C e₃
    χ = (X - Polynomial.C b) * (X - Polynomial.C m) *
      (X - Polynomial.C c) * (X - Polynomial.C d) ∧
      χ - Polynomial.C e₄ = X * cPoly := by
  dsimp
  constructor <;> simp only [map_add, map_mul] <;> ring

end MathlibPlus.Algebra.Claim27203
