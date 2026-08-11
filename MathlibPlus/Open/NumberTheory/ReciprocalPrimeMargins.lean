import Mathlib

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

/-- Claim 619: the exhaustive later-prime margin certificate.

The inclusive prime range and the uniqueness implicit in “the closest competitor
is `293`” are stated explicitly.  The displayed decimal is an exact rational
lower bound. -/
def exhaustiveLaterPrimeMargin : Prop :=
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
      (∀ p : ℕ, Nat.Prime p → 293 ≤ p → p ≤ 2278379 →
        E₁ (p : ℝ) < Cstar) ∧
        (∀ p : ℕ, Nat.Prime p → 293 ≤ p → p ≤ 2278379 →
          E₁ (p : ℝ) ≤ E₁ 293) ∧
        (∀ p : ℕ, Nat.Prime p → 293 ≤ p → p ≤ 2278379 →
          (E₁ (p : ℝ) = E₁ 293 ↔ p = 293)) ∧
        Cstar - E₁ 293 > 0.023352283003699

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
