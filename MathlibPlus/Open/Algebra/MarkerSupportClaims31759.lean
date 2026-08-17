import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769

namespace MathlibPlus.Open.Algebra.MarkerSupportClaims

/-- Claim 31759: divisibility by the primitive linear marker prime, together
with linearity in the largest marker, first yields quotients free of that
marker.  The separate support warning is retained: this does not yet remove
markers above it. -/
def claim31759 : Prop :=
  (∀ (J : ℕ) (p PsiS PsiR : MarkerRing),
    2 ≤ J →
    Prime p →
    (∃ a b : MarkerRing,
      a ≠ 0 ∧
        strictLowerMarker J a ∧
          strictLowerMarker J b ∧
            p = a * MvPolynomial.X J + b) →
    MvPolynomial.degreeOf J PsiS ≤ 1 →
    MvPolynomial.degreeOf J PsiR ≤ 1 →
    p ∣ PsiS →
    p ∣ PsiR →
    ∃ hS hR : MarkerRing,
      PsiS = hS * p ∧
        PsiR = hR * p ∧
          MvPolynomial.degreeOf J hS = 0 ∧
            MvPolynomial.degreeOf J hR = 0) ∧
    degreeOneMarkerAloneInsufficient_claim31768

end MathlibPlus.Open.Algebra.MarkerSupportClaims
