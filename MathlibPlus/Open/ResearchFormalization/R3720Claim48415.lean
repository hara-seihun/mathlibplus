import MathlibPlus.Open.ResearchFormalization.R3720TreeU

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3720

noncomputable section

/-- The component degree of a monomial is the sum of its exponents. -/
def componentDegree (m : ResearchVariable →₀ ℕ) : ℕ :=
  m.sum (fun _ exponent => exponent)

/-- A polynomial is component-homogeneous when its ordinary total degree is fixed. -/
def componentHomogeneous (d : ℕ) (f : ResearchPolynomial) : Prop :=
  MvPolynomial.IsHomogeneous f d

/-- The component-degree `d` part of a polynomial. -/
noncomputable def componentPart (d : ℕ) (f : ResearchPolynomial) : ResearchPolynomial :=
  MvPolynomial.homogeneousComponent d f

/-- The degree of the top nonzero component of a polynomial. -/
def topComponentDegree (f : ResearchPolynomial) : ℕ :=
  MvPolynomial.totalDegree f

/-- The top component-degree part of a polynomial. -/
noncomputable def topComponent (f : ResearchPolynomial) : ResearchPolynomial :=
  componentPart (topComponentDegree f) f

/-- One summand of the finite realization of the derivation `δ`. -/
noncomputable def deltaSummand (a : ResearchVariable) (f : ResearchPolynomial) :
    ResearchPolynomial :=
  MvPolynomial.C (a.1 : ℚ) * MvPolynomial.X (successorVariable a) *
    (MvPolynomial.pderiv a) f

/-- Claim 48415: the component-degree grading gives the top-component
identity and injectivity of the polynomial raising operator. -/
def claim_48415 : Prop :=
  (∀ (m : ResearchVariable →₀ ℕ) (r : ℕ),
      componentDegree m = r →
        componentHomogeneous r (MvPolynomial.monomial m 1)) ∧
    (∀ (f : ResearchPolynomial) (d : ℕ),
      componentHomogeneous d f →
        componentHomogeneous (d + 1)
          (MvPolynomial.X firstVariable * f)) ∧
    (∀ (a : ResearchVariable) (f : ResearchPolynomial) (d : ℕ),
      componentHomogeneous d f →
        componentHomogeneous d (deltaSummand a f)) ∧
    (∀ (n : ℕ) (f : ResearchPolynomial), f ≠ 0 →
      componentPart (topComponentDegree f + 1) (researchGamma n f) =
        MvPolynomial.C (n : ℚ) * MvPolynomial.X firstVariable *
          topComponent f) ∧
    (∀ (n : ℕ) (f : ResearchPolynomial), 0 < n → f ≠ 0 →
      MvPolynomial.C (n : ℚ) * MvPolynomial.X firstVariable *
          topComponent f ≠ 0) ∧
    (∀ (n : ℕ), 0 < n → gammaWeightInjective n)

end
end MathlibPlus.Open.ResearchFormalization.R3720
