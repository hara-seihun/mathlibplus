import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616Claim42829

noncomputable section

open MathlibPlus.Open.Analysis

/-- Claim 42829: the all-real scale-uniform square-root energies of the
named full and odd Möbius transforms are finite together, with the exact
fixed constants from the dyadic coordinate. -/
def claim42829 : Prop :=
  (oneLogCriticalSquareRootNorm fullMobiusTransform ≠ ⊤ ↔
      oneLogCriticalSquareRootNorm oddMobiusTransform ≠ ⊤) ∧
    (ENNReal.ofReal (1 - criticalDyadicQ) *
        oneLogCriticalSquareRootNorm oddMobiusTransform ≤
      oneLogCriticalSquareRootNorm fullMobiusTransform) ∧
    (oneLogCriticalSquareRootNorm fullMobiusTransform ≤
      ENNReal.ofReal (1 + criticalDyadicQ) *
        oneLogCriticalSquareRootNorm oddMobiusTransform)

end

end MathlibPlus.Open.ResearchFormalization.R2616Claim42829
