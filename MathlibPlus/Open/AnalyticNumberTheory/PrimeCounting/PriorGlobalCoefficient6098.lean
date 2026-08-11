import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Prior global coefficient-6098 prime-counting bound

This registry node formalizes admitted claim 630. For real arguments, `π(x)` is
interpreted in the standard way as `Nat.primeCounting ⌊x⌋₊`, so primes at the
integer endpoint are included.
-/

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- For every real `x > 1`, the prime-counting function is strictly below the
packet's eight-term comparison function with eighth coefficient `6098`.

The seven preceding coefficients and the full range `x > 1` are retained
verbatim. -/
def priorGlobalCoefficient6098 : Prop :=
  ∀ x : ℝ, 1 < x →
    let L := Real.log x
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / L + x / L ^ 2 + 2 * x / L ^ 3 +
        ((3012167 : ℝ) / 500000) * x / L ^ 4 +
        ((12012167 : ℝ) / 500000) * x / L ^ 5 +
        ((12012167 : ℝ) / 100000) * x / L ^ 6 +
        ((36036501 : ℝ) / 50000) * x / L ^ 7 +
        6098 * x / L ^ 8

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
