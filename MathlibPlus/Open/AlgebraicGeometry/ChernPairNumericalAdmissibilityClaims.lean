import MathlibPlus.AlgebraicGeometry.Claim16989

namespace MathlibPlus.Open.AlgebraicGeometry

/-- The named numerical Chern-pair predicate is represented by the exact
integer predicate already admitted for numerical geography. -/
def NumericallyAdmissibleChernPair (K2 c2 : ℤ) : Prop :=
  MathlibPlus.AlgebraicGeometry.numericallyAdmissible_claim16989 K2 c2

/-- Claim 14595: the Chern pair `(2, 10)` passes all four elementary filters
encoded by `NumericallyAdmissibleChernPair`. -/
def numericalAdmissibility_claim14595 : Prop :=
  NumericallyAdmissibleChernPair (2 : ℤ) 10

/-- Claim 14609: the Chern pair `(4, 8)` passes all four elementary filters
encoded by `NumericallyAdmissibleChernPair`. -/
def numericalAdmissibility_claim14609 : Prop :=
  NumericallyAdmissibleChernPair (4 : ℤ) 8

end MathlibPlus.Open.AlgebraicGeometry
