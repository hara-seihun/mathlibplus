import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MathlibPlus.Open.Analysis

/--
Exact real form of the Cayley-radius rate inequality.  The displayed rate is
`2 Re(a-1) + d (1 + log (|a-1|^2/d))`; this is the normalization for which
`1 + log u ≤ u` has equality precisely at `u = 1`.  `Complex.normSq` is the
literal squared modulus carrier.
-/
def cayleyRadiusRateInequality_claim4126 : Prop :=
  ∀ (d : ℝ) (a : ℂ), d > 0 → a ≠ 1 →
    let r : ℝ := Complex.normSq (a - 1)
    2 * Complex.re (a - 1) + d * (1 + Real.log (r / d)) ≤
        2 * Complex.re (a - 1) + r ∧
      2 * Complex.re (a - 1) + r = Complex.normSq a - 1 ∧
      (2 * Complex.re (a - 1) + d * (1 + Real.log (r / d)) =
          2 * Complex.re (a - 1) + r ↔ d = r)

end MathlibPlus.Open.Analysis
