import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

/-- Claim 3305: Euler's hyperbolic-sine product, including its continuous value at zero. -/
def eulerHyperbolicSineProduct : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    Filter.Tendsto
      (fun N : ℕ =>
        ∏ m ∈ Finset.Icc 1 N, (1 + a ^ 2 / (m : ℝ) ^ 2))
      Filter.atTop
      (nhds (if a = 0 then 1 else Real.sinh (Real.pi * a) / (Real.pi * a)))

/-- Claim 8735: the exterior resolvent expansion, with the standard
Chebyshev identity T_r(t) = cos(r arccos t) on [-1,1]. -/
def chebyshevExteriorResolventExpansion : Prop :=
  ∀ (ξ t : ℝ), ξ > 1 → -1 ≤ t → t ≤ 1 →
    1 / (ξ - t) =
      1 / Real.sqrt (ξ ^ 2 - 1) *
        (1 + 2 *
          ∑' r : {r : ℕ // 1 ≤ r},
            Real.exp (-(r : ℝ) * Real.arcosh ξ) *
              Real.cos ((r : ℝ) * Real.arccos t))

end MathlibPlus.Open.AdmittedBatch
