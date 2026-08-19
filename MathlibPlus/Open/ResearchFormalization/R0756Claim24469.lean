import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0756Claim24469

/-- The top-three coefficient matrix, with rows indexed by the three
remainders and columns ordered as the coefficients of x^d, x^(d-1), and
x^(d-2). -/
def topThreeCoefficientMatrix {R : Type*} [CommRing R]
    (d : ℕ) (a₀ a₁ a₂ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, (d : R) * a₀, (Nat.choose d 2 : R) * a₀ ^ 2;
     1, (d : R) * a₁, (Nat.choose d 2 : R) * a₁ ^ 2;
     1, (d : R) * a₂, (Nat.choose d 2 : R) * a₂ ^ 2]

/-- Claim 24469: the coefficient-pivot determinant is the displayed
Vandermonde product. -/
def vandermondeCoefficientPivotDet_claim24469 : Prop :=
  ∀ (R : Type*) [CommRing R]
    (d : ℕ) (a₀ a₁ a₂ : R),
    (topThreeCoefficientMatrix d a₀ a₁ a₂).det =
      (d : R) * (Nat.choose d 2 : R) *
        (a₁ - a₀) * (a₂ - a₀) * (a₂ - a₁)

end MathlibPlus.Open.ResearchFormalization.R0756Claim24469
