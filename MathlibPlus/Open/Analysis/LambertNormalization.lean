import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Within the compact Lambert family, the parameter is uniquely determined by
matching its two-term extensive expression with the Riemann--von Mangoldt
normalization `T / (2 * π) * (log (T / (2 * π)) - 1)`.
-/
def uniqueCompactLambertNormalization : Prop :=
  ∀ κ : ℝ, 0 < κ →
    ((∀ T : ℝ, 0 < T →
      (T / (2 * Real.pi)) * (Real.log (T / κ) - 1) =
        (T / (2 * Real.pi)) *
          (Real.log (T / (2 * Real.pi)) - 1)) ↔
      κ = 2 * Real.pi)

end MathlibPlus.Open.Analysis
