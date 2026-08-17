import MathlibPlus.Open.Analysis.ResearchFormalizeR0438
import MathlibPlus.Open.ResearchFormalization.R0521_Claim22290

open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22291

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.ResearchFormalization.R0521.Claim22290

noncomputable section

/-- The instantaneous zero-motion equation, stated with actual coordinate
    derivatives rather than an unconstrained velocity callback. -/
def zeroMotionAt (x : ℝ → ℤ → ℝ) (t : ℝ) : Prop :=
  ∀ (i : ℤ),
    HasDerivAt (fun s : ℝ => x s i)
      (2 * ∑' j : {j : ℤ // j ≠ i}, 1 / (x t i - x t j)) t

/-- The finite profile along a real-time zero configuration. -/
def dynamicProfile (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  symmetricGapProfile (fun i : ℤ => x t i) k r

/-- The exact one-step profile derivative in the dense-tail configuration. -/
def oneStepProfileDerivative (x : ℤ → ℝ) : ℝ :=
  4 / (gap x 0) ^ 2 *
    (gap x 0 * pressure x 1 / gap x 1 -
      gap x 1 * pressure x 0 / gap x 0)

/-- The function appearing in the scaled negative limit. -/
def profileSignFunction (q : ℝ) : ℝ :=
  Real.log (1 + q - q ^ 2) + (2 * q - 1) * Real.log q

/-- Claim 22291: the one-step profile derivative is tied to the actual
    zero-motion derivative semantics, and its explicit dense-tail value has
    the stated negative epsilon-scaled limit. -/
def divergentNegativeProfileDerivative_claim22291 : Prop :=
  ∀ (q : ℝ), 0 < q → q < 1 →
    (∀ (ε : ℝ), 0 < ε →
      symmetricGapProfile (denseTailRoot q ε) 0 1 =
        2 * gap (denseTailRoot q ε) 1 / gap (denseTailRoot q ε) 0 - 2) ∧
    (∀ (ε : ℝ), 0 < ε →
      ∀ (x : ℝ → ℤ → ℝ),
        (∀ i : ℤ, x 0 i = denseTailRoot q ε i) →
        (∀ i : ℤ, 0 < gap (fun j : ℤ => x 0 j) i) →
        zeroMotionAt x 0 →
        HasDerivAt (fun s : ℝ => dynamicProfile x s 0 1)
          (oneStepProfileDerivative (fun i : ℤ => x 0 i)) 0) ∧
    Filter.Tendsto
      (fun ε : ℝ => ε * oneStepProfileDerivative (denseTailRoot q ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (𝓝 (-4 * profileSignFunction q))

end

end MathlibPlus.Open.ResearchFormalization.R0521Claim22291
