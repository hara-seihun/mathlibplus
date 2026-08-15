import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchR0750

/-- Claim 26862, stated over the explicitly named polynomial ring `ℚ[w]`. -/
def claim_26862_monicProjectiveScalarRigidity : Prop :=
  ∀ (D GS GT : Polynomial ℚ) (C : ℚ) (lambda : ℚˣ),
    D ≠ 0 →
    GS.Monic →
    GT.Monic →
    GS.degree = GT.degree →
    D * (GS - (lambda : ℚ) • GT) +
        Polynomial.C ((1 - (lambda : ℚ)) * C) = 0 →
    lambda = 1

end MathlibPlus.Open.Research.FormalizationBatchR0750
