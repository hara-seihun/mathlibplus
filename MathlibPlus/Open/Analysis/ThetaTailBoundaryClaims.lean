import MathlibPlus.Analysis.PullFirstClaim4709
import MathlibPlus.Analysis.ThetaMellin

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Claim 4645, with `T` resolved to the exact positive-index theta tail
already recorded in `MathlibPlus.Analysis.Claim4709`.  This is a registry
proposition, not a proof of the modular endpoint relation. -/
noncomputable def thetaTailKernelDerivative_claim4645 : Prop :=
  deriv (fun u : ℝ => MathlibPlus.Analysis.Claim4709.thetaTail u) 0 =
    -(1 + 2 * MathlibPlus.Analysis.Claim4709.thetaTail 0) / 4

/-- Claim 18844, with the source's `Φ_m` resolved to the completed theta
shells used by `MathlibPlus.Analysis.ThetaMellin`.  The positive-index
summation is represented by the index `m + 1`. -/
noncomputable def completedThetaFirstBoundaryJet_claim18844 : Prop :=
  (∑' m : ℕ,
      deriv (fun u : ℝ => MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u) 0) = 0

/-- Claim 4659, stated for the complete shell sum rather than an arbitrary
finite truncation.  Odd derivatives are indexed as `2 * k + 1`. -/
noncomputable def completedThetaOddJets_claim4659 : Prop :=
  ∀ k : ℕ,
    iteratedDeriv (2 * k + 1)
      MathlibPlus.Analysis.ThetaMellin.completedThetaKernel 0 = 0

end MathlibPlus.Open.Analysis
