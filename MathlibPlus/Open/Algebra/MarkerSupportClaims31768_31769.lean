import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Algebra.MarkerSupportClaims

abbrev MarkerRing := MvPolynomial ℕ ℚ

/-- Marker support strictly below `J`.  Index zero is the scalar variable,
index one is the auxiliary non-marker coordinate, and indices at least two
are the component markers. -/
def strictLowerMarker (J : ℕ) (P : MarkerRing) : Prop :=
  MvPolynomial.degreeOf 1 P = 0 ∧
    ∀ K : ℕ, J ≤ K → MvPolynomial.degreeOf K P = 0

/-- The coefficient face of a multivariate marker polynomial at exponent one
in the distinguished marker. -/
def markerCoefficient (J : ℕ) (P : MarkerRing) : MarkerRing := by
  classical
  exact ∑ d ∈ P.support,
    if d J = 1 then
      MvPolynomial.monomial (d.erase J) (P.coeff d)
    else 0

/-- Weighted support at exact forest order. -/
def markerMonomialOrder (d : ℕ →₀ ℕ) : ℕ :=
  ∑ K ∈ d.support,
    (if K = 0 then 1 else if K = 1 then 0 else K) * d K

def hasTotalMarkerOrderAtMost (r : ℕ) (P : MarkerRing) : Prop :=
  ∀ d ∈ P.support, markerMonomialOrder d ≤ r

/-- Claim 31768: degree one in `c_J` does not by itself force a quotient into
strictly lower markers.  The displayed quotient is `c_(J+1)`, while its
product with a linear prime contains the forbidden weighted term
`c_J c_(J+1)`. -/
def degreeOneMarkerAloneInsufficient_claim31768 : Prop :=
  ∀ (J r : ℕ),
    2 ≤ J → J ≤ r → r < 2 * J →
      let p : MarkerRing := MvPolynomial.X J
      let q : MarkerRing := MvPolynomial.X (J + 1)
      let Psi : MarkerRing := p * q
      Prime p ∧
        MvPolynomial.degreeOf J p ≤ 1 ∧
        MvPolynomial.degreeOf J Psi ≤ 1 ∧
        MvPolynomial.degreeOf J q = 0 ∧
        MvPolynomial.degreeOf (J + 1) p = 0 ∧
        MvPolynomial.degreeOf (J + 1) q = 1 ∧
        ¬strictLowerMarker J q ∧
        Psi = q * p ∧
        ¬hasTotalMarkerOrderAtMost r Psi

/-- Claim 31769: in the exact marker ring, support cancellation in the
coefficient face forces a `c_J`-free quotient to have no marker at or above
`J`. -/
def formallyCheckedGenericQuotientLemma_claim31769 : Prop :=
  ∀ (J : ℕ) (a b h p Psi : MarkerRing),
    2 ≤ J →
    a ≠ 0 →
    strictLowerMarker J a →
    strictLowerMarker J b →
    p = a * MvPolynomial.X J + b →
    Psi = h * p →
    MvPolynomial.degreeOf J Psi ≤ 1 →
    MvPolynomial.degreeOf J h = 0 →
    strictLowerMarker J (markerCoefficient J Psi) →
    strictLowerMarker J h

end MathlibPlus.Open.Algebra.MarkerSupportClaims
