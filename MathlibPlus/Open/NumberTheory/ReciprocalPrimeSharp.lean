import Mathlib

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

/-- Claim 616: the sharp coefficient on the complete range `x ≥ 286`.

`A₁` and `E₁(x) = A₁(x) log² x` are expanded from the packet notation.  The
constant `Cstar` is tied to `E₁(286)`, rather than left as an unconstrained
witness. -/
def sharpSameRangeUpperCoefficient : Prop :=
  let reciprocalPrimeSum : ℝ → ℝ := fun x ↦
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, (p : ℝ)⁻¹
  ∃ B Cstar : ℝ,
    Filter.Tendsto
        (fun x : ℝ ↦ reciprocalPrimeSum x - Real.log (Real.log x))
        Filter.atTop (nhds B) ∧
      let A₁ : ℝ → ℝ := fun x ↦
        reciprocalPrimeSum x - Real.log (Real.log x) - B
      Cstar = A₁ 286 * (Real.log 286) ^ 2 ∧
        (∀ x : ℝ, 286 ≤ x →
          A₁ x ≤ Cstar / (Real.log x) ^ 2) ∧
        (∀ x : ℝ, 286 ≤ x →
          (A₁ x = Cstar / (Real.log x) ^ 2 ↔ x = 286)) ∧
        ∀ C : ℝ,
          (∀ x : ℝ, 286 ≤ x → A₁ x ≤ C / (Real.log x) ^ 2) →
            Cstar ≤ C

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
