import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769

namespace MathlibPlus.Open.ResearchFormalization.R1166

noncomputable section

open MathlibPlus.Open.Algebra.MarkerSupportClaims

/-- Claim 31761: in the exact marker ring, the coefficient-face identities
and the no-higher-marker support force both terminal quotients into the strict
lower-marker subring. -/
def claim31761 : Prop :=
  ∀ (J : ℕ) (a b hS hR p PsiS PsiR : MarkerRing),
    2 ≤ J →
      a ≠ 0 →
        strictLowerMarker J a →
          strictLowerMarker J b →
            p = a * MvPolynomial.X J + b →
              PsiS = hS * p →
                PsiR = hR * p →
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

end
end MathlibPlus.Open.ResearchFormalization.R1166
