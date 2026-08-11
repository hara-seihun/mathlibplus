import Mathlib

namespace MathlibPlus.Logic

/-- Claim 15652: if both branches of a dichotomy imply `¬ C`, then `¬ C`.
`RH` and `C` are left as arbitrary propositions because the source does not
assign them a more specific formal type here. -/
theorem twoBranchLogicalImpossibility_claim15652
    (RH C : Prop) (h_rh : RH → ¬ C) (h_not_rh : ¬ RH → ¬ C) :
    ¬ C := by
  intro hC
  by_cases hRH : RH
  · exact h_rh hRH hC
  · exact h_not_rh hRH hC

end MathlibPlus.Logic
