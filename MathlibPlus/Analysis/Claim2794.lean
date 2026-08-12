import Mathlib

namespace MathlibPlus.Analysis.Claim2794

/-- The exact physical certification rectangle from admitted claim 2794. -/
def physicalCertificationRectangle_claim2794 : Set ℂ :=
  {t | 0.01 ≤ t.re ∧ t.re ≤ 20 ∧ |t.im| ≤ 0.499}

end MathlibPlus.Analysis.Claim2794
