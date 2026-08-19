import MathlibPlus.Open.ResearchFormalization.R1863.Claim34341

namespace MathlibPlus.Open.ResearchFormalization.R1863Claim34343

open MathlibPlus.Open.Algebra.PathSwitchM0
open MathlibPlus.Open.ResearchFormalization.R1863

noncomputable section

private def oneStepExtension : PathRing :=
  N (1 : PathRing)

/-- The formal parent boundary from Claim 34343, using the reviewed
`SameHostPathSwitch`, `N`, and root-marker selector. -/
def parentBoundary_claim34343
    (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A (oneStepExtension *
    (S.P * N^[k] S.Q - S.Q * N^[k] S.P))

/-- The positive smaller boundary from Claim 34343. -/
def smallerPositiveBoundary_claim34343
    (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A (E k * S.P)

/-- The negative smaller boundary from Claim 34343. -/
def smallerNegativeBoundary_claim34343
    (S : SameHostPathSwitch) (k : ℕ) : PathRing :=
  A (E k * S.Q)

end

end MathlibPlus.Open.ResearchFormalization.R1863Claim34343
