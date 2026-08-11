import Mathlib

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

/-- Claim 622: the normalized analytic handoff from the log-cubed tail.

The two reported handoff margins are interpreted as lower bounds for
`Cstar - 1 / (5 log 2278383)`, exactly as in the packet's displayed handoff. -/
def normalizedAnalyticHandoff : Prop :=
  let reciprocalPrimeSum : ℝ → ℝ := fun x ↦
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, (p : ℝ)⁻¹
  ∃ B : ℝ,
    Filter.Tendsto
        (fun x : ℝ ↦ reciprocalPrimeSum x - Real.log (Real.log x))
        Filter.atTop (nhds B) ∧
      let A₁ : ℝ → ℝ := fun x ↦
        reciprocalPrimeSum x - Real.log (Real.log x) - B
      let E₁ : ℝ → ℝ := fun x ↦ A₁ x * (Real.log x) ^ 2
      let Cstar : ℝ := E₁ 286
      ((∀ x : ℝ, 2278383 ≤ x →
          |A₁ x| ≤ 1 / (5 * (Real.log x) ^ 3)) →
        ∀ x : ℝ, 2278383 ≤ x →
          E₁ x ≤ 1 / (5 * Real.log x) ∧
            1 / (5 * Real.log x) ≤ 1 / (5 * Real.log 2278383) ∧
            1 / (5 * Real.log 2278383) < Cstar) ∧
        Cstar - 1 / (5 * Real.log 2278383) > 0.4735 ∧
        Cstar - 1 / (5 * Real.log 2278383) > 0.473

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
