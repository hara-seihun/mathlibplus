import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15424

open Asymptotics Filter MeasureTheory Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias

noncomputable section

/-- Claim 15421: a fixed Sobolev order has one order-dependent Fourier-decay
constant, uniformly over the endpoint-flat sources at every logarithmic
scale. -/
def claim15421_fourierDecayFromEndpointTraces : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∃ C_N : ℝ, 0 ≤ C_N ∧
      ∀ (L : ℝ) (q : ℝ → ℝ),
        wN1Chain N q →
          (∀ j : ℕ, j < N →
            iteratedDeriv j q (Real.exp L) = 0 ∧
              iteratedDeriv j q (-(Real.exp L)) = 0) →
            ∀ ξ : ℝ, ξ ≠ 0 →
              ‖poissonFourierTransform q ξ‖ ≤
                C_N * derivativeL1Norm N q *
                  Real.rpow |ξ| (-(N : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias
