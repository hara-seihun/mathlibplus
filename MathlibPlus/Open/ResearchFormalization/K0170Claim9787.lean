import MathlibPlus.Open.ResearchFormalizationBatch_01a0032b.Prime
import MathlibPlus.Open.Analysis.HigherPrimePowerEndpoint

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.K0170Claim9787

noncomputable section

open MathlibPlus.Open.Batch_01a0032b
open MathlibPlus.Open.Analysis

abbrev PrimeIndex9787 :=
  MathlibPlus.Open.Batch_01a0032b.PrimeIndex

/-- The primewise derivative majorant on the half-plane boundary. -/
def primeDerivativeMajorant (σ : ℝ) (p : PrimeIndex9787) : ℝ :=
  Real.log (p.1 : ℝ) * Real.rpow (p.1 : ℝ) (-σ)

/-- The squared prime derivative budget. -/
noncomputable def primeDerivativeBudget (σ ℓ : ℝ) : ℝ :=
  (∑' p : PrimeIndex9787,
    (Real.log (p.1 : ℝ)) ^ 2 * Real.rpow (p.1 : ℝ) (-2 * σ)) * ℓ ^ 2

/-- Claim 9787: the exact short-arc endpoint estimate holds at every prime,
and the endpoint functional has the displayed squared dual-norm budget. -/
def claim9787 : Prop :=
  ∀ (σ ℓ : ℝ) (a b : ℂ),
    1 / 2 < σ →
    MathlibPlus.Open.Analysis.shortArcInHalfPlane σ ℓ a b →
      (∀ p : PrimeIndex9787,
        ‖endpointCoefficient a b p‖ ≤
          ℓ * primeDerivativeMajorant σ p) ∧
      Summable (fun p : PrimeIndex9787 =>
        (Real.log (p.1 : ℝ)) ^ 2 *
          Real.rpow (p.1 : ℝ) (-2 * σ)) ∧
      endpointDualNormSquared a b ≤ primeDerivativeBudget σ ℓ

end

end MathlibPlus.Open.ResearchFormalization.K0170Claim9787
