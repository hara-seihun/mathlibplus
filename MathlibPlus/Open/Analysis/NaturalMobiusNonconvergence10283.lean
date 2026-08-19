import Mathlib

open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.Analysis

/-- Claim 10283: the prescribed natural Möbius Hardy norm sequence at
`α = 1/2` has no finite limit. -/
def claim10283 : Prop :=
  let A : ℕ → ℝ := fun n =>
    ∑ k ∈ Finset.Icc 1 n,
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)
  let R : ℕ → ℕ → ℝ := fun n j =>
    (j : ℝ) * A n +
      ∑ k ∈ Finset.Icc (n + 1) j,
        (ArithmeticFunction.moebius k : ℝ) * ((j / k : ℕ) : ℝ)
  let s : ℕ → ℝ → ℝ := fun n α =>
    (1 / (2 * α)) *
      ∑' j : ℕ,
        if 1 ≤ j then
          (R n j) ^ 2 *
            (Real.rpow (j : ℝ) (-2 * α) -
              Real.rpow ((j + 1 : ℕ) : ℝ) (-2 * α))
        else 0
  ¬ ∃ L : ℝ,
      Tendsto (fun n : ℕ => s n (1 / 2)) atTop (𝓝 L)

end MathlibPlus.Open.Analysis
