import MathlibPlus.LinearAlgebra.Claim17286

open Set

namespace MathlibPlus.Open.ResearchFormalization.R0025.Claim17287

private def oneChannelPositivitySet {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) : Set ℝ :=
  {x : ℝ | 0 < x ∧ (A + x • B).PosSemidef}

/-- Claim 17287: the intersection of the two exact positive-parameter
channel feasibility sets is an interval, with empty and unbounded intervals
allowed. -/
def claim17287 {N : ℕ}
    (A0 B0 Aplus Bplus : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  let I0 := oneChannelPositivitySet A0 B0
  let Iplus := oneChannelPositivitySet Aplus Bplus
  let C := I0 ∩ Iplus
  C.OrdConnected

end MathlibPlus.Open.ResearchFormalization.R0025.Claim17287
