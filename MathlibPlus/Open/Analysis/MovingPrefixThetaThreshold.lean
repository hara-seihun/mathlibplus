import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 59843: a uniform bound obtained from the successive-difference estimate. -/
def exists_constants_uniformly_ge_frac_pi_sqrt_left_frac_infty_moving_prefix_theta_threshold
    (p : ℕ → ℝ) (q C A N : ℝ) (M : ℕ) : Prop :=
  q ≠ 0 →
    0 ≤ C →
      0 ≤ N →
        Filter.Tendsto p Filter.atTop (nhds q) →
          (((M + 1 : ℕ) : ℝ) ^ 2 ≥
            (3 / (2 * Real.pi)) * N + A * Real.sqrt N) →
            (∀ k : ℕ,
              |(p (M + k + 1) - p (M + k)) / q| ≤
                C * N ^ A *
                  Real.exp ((3 / 2 : ℝ) * N -
                    Real.pi * (((M + k + 1 : ℕ) : ℝ) ^ 2))) →
              |(q - p M) / q| ≤
                C * N ^ A * Real.exp (-Real.pi * A * Real.sqrt N) /
                  (1 - Real.exp (-Real.pi))

end MathlibPlus.Open.Analysis
