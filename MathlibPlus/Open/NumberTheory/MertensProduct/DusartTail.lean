import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

namespace MathlibPlus.Open.NumberTheory.MertensProduct

/-!
The normalized error is expanded from the admitted definition
`E(x) = log x * (exp(-gamma) * P(x) - log x)` so the tail claim remains
self-contained.
-/

/-- Dusart's Mertens-product tail and its two stated normalized-error
consequences. -/
def dusartTail : Prop :=
  let primeProduct : ℝ → ℝ := fun x ↦
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)
  let normalizedError : ℝ → ℝ := fun x ↦
    Real.log x *
      (Real.exp (-Real.eulerMascheroniConstant) * primeProduct x - Real.log x)
  ∀ x : ℝ, 2278382 ≤ x →
    primeProduct x ≤
        Real.exp Real.eulerMascheroniConstant * Real.log x *
          (1 + 1 / (5 * Real.log x ^ 3)) ∧
      normalizedError x ≤ 1 / (5 * Real.log x) ∧
      1 / (5 * Real.log x) < (0.013663 : ℝ)

end MathlibPlus.Open.NumberTheory.MertensProduct
