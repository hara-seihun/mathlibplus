import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Algebra.Claim23183

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The five rooted-factor test elements used by the scalar defect. -/
def scalarS23183 : RootRing := rootClosure (1 : RootRing)
def scalarE23183 : RootRing := rootClosure scalarS23183
def scalarP23183 : RootRing := rootClosure scalarE23183
def scalarC23183 : RootRing := rootClosure (scalarS23183 ^ 2)
def scalarQ23183 : RootRing := scalarE23183 - scalarS23183 ^ 2

/-- The exact ambient polynomial displayed for the scalar defect. -/
def scalarDefectPolynomial23183 : RootRing :=
  rootZ * rootX 3 + 3 * rootZ * rootX 2 * rootX 1 - rootZ ^ 3 * rootX 1 -
    3 * rootZ ^ 2 * rootX 1 ^ 2 + rootX 3 * rootX 1 +
    rootX 2 * rootX 1 ^ 2 - rootZ * rootX 1 ^ 3 - rootX 2 ^ 2

/-- Coefficient of the ambient monomial `x₂²` (at `z`-degree zero). -/
def x₂SquaredCoefficient23183 (P : RootRing) : ℚ :=
  MvPolynomial.coeff (Finsupp.single 1 2) (P.coeff 0)

/-- The scalar defect equals the displayed polynomial, whose `x₂²` coefficient
is `-1` and hence is nonzero. -/
def explicitNonzeroScalarDefectPolynomial_claim23183 : Prop :=
  scalarS23183 * (scalarP23183 - scalarS23183 * scalarE23183) -
      scalarQ23183 ^ 2 = scalarDefectPolynomial23183 ∧
    x₂SquaredCoefficient23183 scalarDefectPolynomial23183 = (-1 : ℚ) ∧
    scalarDefectPolynomial23183 ≠ 0

end

end MathlibPlus.Algebra.Claim23183
