import MathlibPlus.Open.ResearchFormalization.R1575Claim39300

namespace MathlibPlus.Open.ResearchFormalization.R1575Claim39303

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1575Claim39300

abbrev F7 := MathlibPlus.Open.ResearchFormalization.R1575Claim39300.F7
abbrev F3 := MathlibPlus.Open.ResearchFormalization.R1575Claim39300.F3
abbrev H := MathlibPlus.Open.ResearchFormalization.R1575Claim39300.H
abbrev W := MathlibPlus.Open.ResearchFormalization.R1575Claim39300.W


def tauModU (tau : H → W) (h : H) : F7 :=
  (tau h).2

def activeQuotientRows (tau : H → W) : Set H :=
  {h | ∀ k : H,
    tauModU tau (hMul h k) = tauModU tau h + chi h * tauModU tau k}

/-- Claim 39303: the displayed defect identity is part of the conclusion,
and its active quotient rows form a subgroup of the exact nonabelian carrier.
-/
def claim_39303 : Prop :=
  ∀ (lam : H → F7) (tau : H → W),
    normalizedProfile lam tau →
      (∀ h l k : H,
        defect tau (hMul h l) k =
          defect tau h (hMul l k) - defect tau h l +
            chi h • defect tau l k) ∧
        hSubgroup (activeQuotientRows tau)

end

end MathlibPlus.Open.ResearchFormalization.R1575Claim39303
