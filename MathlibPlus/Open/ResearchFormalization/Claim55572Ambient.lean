import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R5524

noncomputable section

abbrev AmbientRing := MvPolynomial ℕ ℤ
abbrev SourcePolynomial := Polynomial AmbientRing

/-- The ambient variables are `z` at index zero and `x_j` at index `j≥1`. -/
def zVariable : AmbientRing := MvPolynomial.X 0

def xVariable (j : ℕ) : AmbientRing := MvPolynomial.X j

/-- The component-card shift on ambient monomials, with the distinguished
`z` exponent sent to the new `x` index. -/
def phi (s : ℕ) (P : AmbientRing) : AmbientRing :=
  ∑ d ∈ P.support,
    P.coeff d •
      (xVariable (d 0 + s) *
        MvPolynomial.monomial (d - Finsupp.single 0 (d 0)) 1)

/-- Diagonal specialization: `z` becomes the polynomial variable `t`, while
every `x_j` remains a coefficient variable. -/
def diagonalMap : AmbientRing →+* SourcePolynomial :=
  MvPolynomial.eval₂Hom
    (algebraMap ℤ SourcePolynomial)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C (xVariable i))

def diagonalSpecialization (P : AmbientRing) : SourcePolynomial :=
  diagonalMap P

/-- Coefficientwise extension of the component-card shift to polynomials in
the diagonal variable. -/
def phiPolynomial (s : ℕ) (P : SourcePolynomial) : SourcePolynomial :=
  ∑ n ∈ P.support, Polynomial.C (phi s (P.coeff n)) * Polynomial.X ^ n

/-- The scalar socket response `B(P,Q)`. -/
def scalarBPolynomial (P Q : SourcePolynomial) : SourcePolynomial :=
  phiPolynomial 1 P * phiPolynomial 1 Q + phiPolynomial 2 (P * Q)

def scalarB (P Q : AmbientRing) : SourcePolynomial :=
  scalarBPolynomial (Polynomial.C P) (Polynomial.C Q)

/-- The finite set of source variables needed by the formal derivative. -/
def sourceVariableSet (P : AmbientRing) : Finset ℕ :=
  (P.support.biUnion (fun d => d.support)).filter (fun j => 1 ≤ j)

/-- The source derivative `V_t = Σ j≥1 t^(j-1) ∂_(x_j)`. -/
def sourceDerivative (P : AmbientRing) : SourcePolynomial :=
  ∑ j ∈ sourceVariableSet P,
    Polynomial.C (MvPolynomial.pderiv j P) * Polynomial.X ^ (j - 1)

/-- Apply the source derivative coefficientwise to a polynomial in `t`. -/
def sourceDerivativeOnPolynomial
    (P : SourcePolynomial) : SourcePolynomial :=
  ∑ n ∈ P.support, sourceDerivative (P.coeff n) * Polynomial.X ^ n

/-- The first diagonal cross-effect, extended bilinearly in the source
polynomial arguments. -/
def diagonalCrossEffectPolynomial
    (P Q : SourcePolynomial) : SourcePolynomial :=
  sourceDerivativeOnPolynomial (scalarBPolynomial P Q) -
    scalarBPolynomial (sourceDerivativeOnPolynomial P) Q -
    scalarBPolynomial P (sourceDerivativeOnPolynomial Q)

def diagonalCrossEffect (P Q : AmbientRing) : SourcePolynomial :=
  diagonalCrossEffectPolynomial (Polynomial.C P) (Polynomial.C Q)

/-- The diagonal source response `H_t` from the second cross-effect. -/
def diagonalSourceResponse (P Q : AmbientRing) : SourcePolynomial :=
  sourceDerivativeOnPolynomial (diagonalCrossEffect P Q) -
    diagonalCrossEffectPolynomial (sourceDerivative P) (Polynomial.C Q) -
    diagonalCrossEffectPolynomial (Polynomial.C P) (sourceDerivative Q)

/-- The explicit ambient six-cycle marker polynomial. -/
def d6 : AmbientRing :=
  zVariable * xVariable 1 * xVariable 4 -
      zVariable ^ 2 * xVariable 1 * xVariable 3 -
    xVariable 2 * xVariable 4 +
      zVariable ^ 2 * xVariable 2 ^ 2 +
    xVariable 3 ^ 2 -
      zVariable * xVariable 2 * xVariable 3

/-- Claim 55572: the ambient D₆ marker has zero scalar traces and a nonzero
diagonal source response for the displayed formal pair. -/
def claim55572 : Prop :=
  phi 1 d6 = 0 ∧
    phi 2 d6 = 0 ∧
    diagonalSpecialization d6 ≠ 0 ∧
    scalarB 1 d6 = scalarB 0 0 ∧
    diagonalSourceResponse 1 d6 ≠ diagonalSourceResponse 0 0

end

end MathlibPlus.Open.ResearchFormalization.R5524
