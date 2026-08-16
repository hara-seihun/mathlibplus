import Mathlib

namespace MathlibPlus.Open.Analysis.Claim13423

open MeasureTheory
noncomputable section

/-- The primes at or below a finite cutoff. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

/-- The primorial attached to the sharp prime prefix. -/
def primorial (y : ℕ) : ℕ :=
  Finset.prod (primeCutoff y) (fun p => p)

/-- The differentiated sharp-prefix kernel from the admitted construction. -/
def sharpKernel (y : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Nat.divisors (primorial y)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        Real.rpow (d : ℝ) (-2) * Real.exp (-x / (d : ℝ)))

/-- The weighted square energy `E_y(c) = ∫₀∞ |K_y(x)|² x^(2c-1) dx`. -/
noncomputable def sharpEnergy (y : ℕ) (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (sharpKernel y x) ^ 2 * Real.rpow x (2 * c - 1)

/-- The real prime sum `L_y(σ) = ∑_{p ≤ y} p^(-σ)`. -/
def primeLogSum (y : ℕ) (σ : ℝ) : ℝ :=
  Finset.sum (primeCutoff y) (fun p => Real.rpow (p : ℝ) (-σ))

/--
For every `1 < c < 3/2`, the sharp-prefix energy has the two stated
asymptotic equivalents and diverges, with `σ = 2 - c`.
-/
def unconditionalSharpPrefixEdgeResonance : Prop :=
  ∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
    let σ : ℝ := 2 - c
    Asymptotics.IsEquivalent Filter.atTop
        (fun y : ℕ => Real.log (sharpEnergy y c))
        (fun y : ℕ => 2 * primeLogSum y σ) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun y : ℕ => 2 * primeLogSum y σ)
        (fun y : ℕ =>
          2 * Real.rpow (y : ℝ) (c - 1) /
            ((c - 1) * Real.log (y : ℝ))) ∧
      Filter.Tendsto (fun y : ℕ => sharpEnergy y c)
        Filter.atTop Filter.atTop

end
end MathlibPlus.Open.Analysis.Claim13423
