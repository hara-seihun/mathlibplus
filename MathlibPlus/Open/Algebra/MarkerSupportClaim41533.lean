import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769

namespace MathlibPlus.Open.Algebra.MarkerSupportClaims

/-- Claim 41533: in the exact integral marker ring, the lower-support
coefficient condition forces the quotient factor into the strict lower-marker
subring. -/
def formallyCheckedGenericQuotientLemma_claim41533 : Prop :=
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
