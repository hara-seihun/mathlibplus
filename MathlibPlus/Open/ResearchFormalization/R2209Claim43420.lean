import MathlibPlus.Open.ResearchFormalization.R2209Claim43423

namespace MathlibPlus.Open.ResearchFormalization.R2209Claim43420

open MathlibPlus.Open.ResearchFormalization.R2209Claim43423

noncomputable section

def lowerTopDifference (c : LowerTopCoefficients)
    (r y : QuotientPoint) : F3 :=
  lowerTop c (y + r) - lowerTop c y - lowerTop c r

/-- Claim 43420: a shared projective top line between two distinct
 decomposable switching planes forces the lower-top difference operator to
 vanish at every carry cell and lower-shear-independent quotient direction. -/
def sharedLineForcesLowerTopJetZero_claim43420 : Prop :=
  ∀ (c : LowerTopCoefficients) (q : QuotientPoint → F3),
    q 0 = 0 →
      let F := chartFunction c q
      chartSharedTopLine F →
        ∀ (r y : QuotientPoint), lowerTopDifference c r y = 0

end

end MathlibPlus.Open.ResearchFormalization.R2209Claim43420
