import Mathlib

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

/-- Claim 621: the corrected reciprocal-prime tail estimate.

The finite sum uses `Nat.floor x + 1`, hence ranges over exactly the primes
`p ≤ x`.  The Meissel--Mertens constant is identified by its defining limit;
`A₁(x)` is expanded rather than left as packet notation. -/
def correctedTailEstimate : Prop :=
  let reciprocalPrimeSum : ℝ → ℝ := fun x ↦
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, (p : ℝ)⁻¹
  ∃ B : ℝ,
    Filter.Tendsto
        (fun x : ℝ ↦ reciprocalPrimeSum x - Real.log (Real.log x))
        Filter.atTop (nhds B) ∧
      ∀ x : ℝ, 2278383 ≤ x →
        |reciprocalPrimeSum x - Real.log (Real.log x) - B| ≤
          1 / (5 * (Real.log x) ^ 3)

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
