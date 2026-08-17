import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769

namespace MathlibPlus.Open.ResearchFormalization.R1166.StrictLowerMarker

open MathlibPlus.Open.Algebra.MarkerSupportClaims

/-- Claim 41525: in the one-largest-marker band, the support-controlled
coefficient cancellation puts both terminal quotients in the strict lower
marker ring, rather than merely removing the distinguished marker. -/
def strictLowerMarkerQuotient_claim41525 : Prop :=
  ∀ (J r : ℕ) (a b p PsiS PsiR hS hR : MarkerRing),
    2 ≤ J →
    J ≤ r →
    r < 2 * J →
    Prime p →
    a ≠ 0 →
    strictLowerMarker J a →
    strictLowerMarker J b →
    p = a * MvPolynomial.X J + b →
    PsiS = hS * p →
    PsiR = hR * p →
    hasTotalMarkerOrderAtMost r PsiS →
    hasTotalMarkerOrderAtMost r PsiR →
    MvPolynomial.degreeOf J PsiS ≤ 1 →
    MvPolynomial.degreeOf J PsiR ≤ 1 →
    MvPolynomial.degreeOf J hS = 0 →
    MvPolynomial.degreeOf J hR = 0 →
    strictLowerMarker J (markerCoefficient J PsiS) →
    strictLowerMarker J (markerCoefficient J PsiR) →
      markerCoefficient J PsiS = a * hS ∧
        markerCoefficient J PsiR = a * hR ∧
        strictLowerMarker J hS ∧
        strictLowerMarker J hR

end MathlibPlus.Open.ResearchFormalization.R1166.StrictLowerMarker
