import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

namespace MathlibPlus.Open.NumberTheory

/-- The sharp coefficient in the Mertens prime-product upper bound on
`[286, ∞)`, including uniqueness of the equality point. -/
def sharpMertensPrimeProductCoefficient : Prop :=
  let primeProduct : ℝ → ℝ := fun x ↦
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)
  let gamma : ℝ := Real.eulerMascheroniConstant
  let coefficient : ℝ :=
    Real.log 286 *
      (Real.exp (-gamma) * primeProduct 283 - Real.log 286)
  let admissible : Set ℝ :=
    {C | ∀ x : ℝ, 286 ≤ x →
      primeProduct x ≤
        Real.exp gamma * Real.log x + C * Real.exp gamma / Real.log x}
  IsLeast admissible coefficient ∧
    ∀ x : ℝ, 286 ≤ x →
      (primeProduct x =
        Real.exp gamma * Real.log x +
          coefficient * Real.exp gamma / Real.log x ↔ x = 286)

end MathlibPlus.Open.NumberTheory
