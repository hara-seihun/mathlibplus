import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616Claim42828

noncomputable section

open MathlibPlus.Open.Analysis

/-- Claim 42828: the named Möbius transform and its named critical
coordinate have equal square energies after the logarithmic substitution on
all positive multiplicative windows. -/
def claim42828 : Prop :=
  ∀ a : ℝ, 0 < a →
    (∫ x in (a / Real.exp 1)..a, |fullMobiusTransform x| ^ 2) =
      (∫ y in (-Real.log a)..(-Real.log a + 1),
        |criticalFullField y| ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.R2616Claim42828
