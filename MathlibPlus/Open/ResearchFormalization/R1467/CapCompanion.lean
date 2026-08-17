import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1467

noncomputable section

abbrev ComponentPolynomial := MvPolynomial ℕ ℤ

def witnessW : ComponentPolynomial :=
  MvPolynomial.X 3 ^ 3 -
      2 * MvPolynomial.X 2 * MvPolynomial.X 3 * MvPolynomial.X 4 +
    MvPolynomial.X 2 ^ 2 * MvPolynomial.X 5 -
      MvPolynomial.X 4 * MvPolynomial.X 5 +
    MvPolynomial.X 3 * MvPolynomial.X 6

def exponentX3Cubed : ℕ →₀ ℕ := Finsupp.single 3 3

def exponentX2X3X4 : ℕ →₀ ℕ :=
  Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 4 1

/-- Claim 37530: the exact order-nine witness has cap coefficient `1` and
companion coefficient `-2`, not the forced-Hankel value `-3`. -/
def claim37530_capAndCompanionCoefficients : Prop :=
  MvPolynomial.coeff exponentX3Cubed witnessW = 1 ∧
    MvPolynomial.coeff exponentX2X3X4 witnessW = -2 ∧
    MvPolynomial.coeff exponentX2X3X4 witnessW ≠ -3

end

end MathlibPlus.Open.ResearchFormalization.R1467
