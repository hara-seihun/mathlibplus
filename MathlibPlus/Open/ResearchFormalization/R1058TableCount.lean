import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1058TableCount

noncomputable section

open Classical

/-- Claim 29898: the exact support/coefficient-vector table carrier has
`binom(9,3)=84` supports, `3^3-1=26` nonzero coefficient vectors, and
`84·26^3=1,476,384` tables. -/
def exactSupportCoefficientTableCount_claim29898 : Prop :=
  let Support := {S : Finset (Fin 9) // S.card = 3}
  let CoefficientVector := {v : Fin 3 → ZMod 3 // v ≠ 0}
  let Table := Support × (Fin 3 → CoefficientVector)
  Fintype.card Support = 84 ∧
    Fintype.card CoefficientVector = 26 ∧
    Fintype.card Table = 1_476_384 ∧
    Fintype.card Support * (Fintype.card CoefficientVector) ^ 3 =
      Fintype.card Table

end

end MathlibPlus.Open.ResearchFormalization.R1058TableCount
