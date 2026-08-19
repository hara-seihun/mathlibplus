import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

namespace MathlibPlus.Open.ResearchFormalization.R1157PeriodTwoCode

noncomputable section

open MathlibPlus.Open.GraphTheory.R1168

/-- Claims 31665 and 41429: the exact period-two profile map on the reviewed
`ZMod 5 × Fin 8` base is an injective linear parametrization of the standard
odd solution space, whose function-space dimension and cardinality are five
and `7^5=16807`. -/
def exactFiveDimensionalPeriodTwoVoltageCode_claim31665_41429 : Prop :=
  Function.Injective (periodTwoProfile :
    (ZMod 5 → ZMod 7) → Profile) ∧
    (∀ f g : ZMod 5 → ZMod 7,
      periodTwoProfile (f + g) =
        periodTwoProfile f + periodTwoProfile g) ∧
    (∀ a : ZMod 7, ∀ f : ZMod 5 → ZMod 7,
      periodTwoProfile (a • f) = a • periodTwoProfile f) ∧
    Set.range periodTwoProfile = standardOddUnresolvedSpace ∧
    Module.finrank (ZMod 7) (ZMod 5 → ZMod 7) = 5 ∧
    Set.Finite standardOddUnresolvedSpace ∧
    Set.ncard standardOddUnresolvedSpace = 7 ^ 5 ∧
    Set.ncard standardOddUnresolvedSpace = 16807

end

end MathlibPlus.Open.ResearchFormalization.R1157PeriodTwoCode
