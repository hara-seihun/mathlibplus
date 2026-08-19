import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616Claim42827

open scoped BigOperators
open MathlibPlus.Open.Analysis

noncomputable section

/-- The extended-real uniform-local `L²` norm on all real unit windows. -/
noncomputable def uniformLocalL2Norm (f : ℝ → ℝ) : ENNReal :=
  ⨆ Y : ℝ,
    ENNReal.rpow
      (∫⁻ y in Set.Icc Y (Y + 1), ENNReal.ofReal (|f y| ^ 2))
      (1 / 2 : ℝ)

/-- Claim 42827: the full and odd critical coordinates have the exact
uniform-local norm comparison with `q = 2^(-1/2)`, with no finiteness
hypothesis added. -/
def claim42827 : Prop :=
  let U := criticalOddField
  let G := criticalFullField
  let q := criticalDyadicQ
  ENNReal.ofReal (1 - q) * uniformLocalL2Norm U ≤ uniformLocalL2Norm G ∧
    uniformLocalL2Norm G ≤ ENNReal.ofReal (1 + q) * uniformLocalL2Norm U

end

end MathlibPlus.Open.ResearchFormalization.R2616Claim42827
