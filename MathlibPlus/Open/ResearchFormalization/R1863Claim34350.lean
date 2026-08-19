import MathlibPlus.Open.ResearchFormalization.R1863.Claim34341

namespace MathlibPlus.Open.ResearchFormalization.R1863Claim34350

open MathlibPlus.Open.Algebra.PathSwitchM0
open MathlibPlus.Open.ResearchFormalization.R1863

noncomputable section

private def oneStepExtension : PathRing :=
  N (1 : PathRing)

/-- Claim 34350: on the canonical integral PathRing and reviewed
`SameHostPathSwitch`, a nonzero host and zero parent boundary force equality of
both smaller boundaries. -/
def claim34350 : Prop :=
  ∀ (S : SameHostPathSwitch) (k : ℕ),
    S.U_H ≠ 0 →
      A (oneStepExtension *
        (S.P * N^[k] S.Q - S.Q * N^[k] S.P)) = 0 →
      A (E k * S.P) = A (E k * S.Q)

end

end MathlibPlus.Open.ResearchFormalization.R1863Claim34350
