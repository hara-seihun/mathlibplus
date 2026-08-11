import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalPrime

/-- Certified decimal prefixes and exact rational comparisons for the splice coefficient
`C₀ = 1 / (20 log (10⁸)) + 3 / (16 log² (10⁸))`.

The two displayed decimal expansions from the source are represented by half-open
intervals of width one unit in their final displayed decimal place. All decimal
literals are exact rational numbers in `ℝ`.
-/
def certifiedSpliceCoefficientComparisons : Prop :=
  let L : ℝ := Real.log (10 ^ 8 : ℝ)
  let C₀ : ℝ := 1 / (20 * L) + 3 / (16 * L ^ 2)
  18.4206807439523654721439316374749 ≤ L ∧
    L < 18.4206807439523654721439316374750 ∧
    0.003266913842984036606081159737267 ≤ C₀ ∧
    C₀ < 0.003266913842984036606081159737268 ∧
    0.0000010600132251 < 1 / 306 - C₀ ∧
    0.0000095848527560 < C₀ - 1 / 307 ∧
    153 < (1 / 2) / C₀

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalPrime
