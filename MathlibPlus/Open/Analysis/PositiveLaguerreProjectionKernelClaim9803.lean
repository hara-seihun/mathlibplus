import Mathlib
import MathlibPlus.Open.Analysis.Claim9802
import MathlibPlus.Open.Analysis.Claim9805

open scoped BigOperators
open Filter MeasureTheory Set

noncomputable section

namespace MathlibPlus.Open.Analysis.PositiveLaguerreProjectionKernelClaim9803

private noncomputable def kernel9803 (M : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    generalizedLaguerreOne (n - 1) x * generalizedLaguerreOne (n - 1) y / (n : ℝ)

private noncomputable def weightedInner9803 (f g : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    t * Real.exp (-t) * f t * g t ∂MeasureTheory.volume

private noncomputable def quadraticForm9803 (M : ℕ) (ν : SignedMeasure ℝ) : ℝ :=
  ν.integral
    (fun x =>
      ν.integral (fun y => kernel9803 M x y)
        (ContinuousLinearMap.lsmul ℝ ℝ))
    (ContinuousLinearMap.lsmul ℝ ℝ)

/-- Claim 9803: the explicitly normalized finite Laguerre sum is the finite
orthogonal-projection kernel for the parameter-one Laguerre family in the
weighted space `L²(t exp(-t) dt)`, and its signed-measure quadratic form is
positive semidefinite. -/
def positiveLaguerreProjectionKernel_claim9803 : Prop :=
  (∀ M : ℕ, ∀ x y : ℝ,
    kernel9803 M x y =
      ∑ n ∈ Finset.Icc 1 M,
        generalizedLaguerreOne (n - 1) x * generalizedLaguerreOne (n - 1) y /
          (n : ℝ)) ∧
  (∀ k ℓ : ℕ, k ≠ ℓ →
    weightedInner9803 (generalizedLaguerreOne k)
        (generalizedLaguerreOne ℓ) = 0) ∧
  (∀ k : ℕ,
    weightedInner9803 (generalizedLaguerreOne k)
        (generalizedLaguerreOne k) = ((k + 1 : ℕ) : ℝ)) ∧
  (∀ (M k : ℕ) (x : ℝ), k + 1 ≤ M →
    weightedInner9803
      (fun t => kernel9803 M x t)
      (generalizedLaguerreOne k) = generalizedLaguerreOne k x) ∧
  (∀ (M : ℕ) (ν : SignedMeasure ℝ),
    0 ≤ quadraticForm9803 M ν)

end MathlibPlus.Open.Analysis.PositiveLaguerreProjectionKernelClaim9803
