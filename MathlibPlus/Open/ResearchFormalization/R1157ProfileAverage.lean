import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

namespace MathlibPlus.Open.ResearchFormalization.R1157ProfileAverage

noncomputable section

open MathlibPlus.Open.GraphTheory.R1168

/-- Claim 31669: the exact reviewed profile average of the period-two
voltage profile is `f(0)/2`, and vanishes exactly when `f(0)=0`. -/
def periodTwoProfileAverage_claim31669 : Prop :=
  Fintype.card Base = 40 ∧
    ∀ f : ZMod 5 → ZMod 7,
    profileAverage (periodTwoProfile f) = f 0 * (2 : ZMod 7)⁻¹ ∧
      (profileAverage (periodTwoProfile f) = 0 ↔ f 0 = 0)

end

end MathlibPlus.Open.ResearchFormalization.R1157ProfileAverage
