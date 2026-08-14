import Mathlib

open Filter
open scoped BigOperators Interval Topology

namespace MathlibPlus.Open.Analysis

noncomputable def halfDensityPrimeTower (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ,
    (((Real.log (p : ℝ)) /
        Real.rpow (p : ℝ) (((k + 1 : ℕ) : ℝ) / 2)) : ℂ) *
      Complex.exp
        (-Complex.I * ((k + 1 : ℕ) : ℂ) * (t : ℂ) *
          (Real.log (p : ℝ) : ℂ))

noncomputable def finitePrimeTowerSum (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, halfDensityPrimeTower p t

noncomputable def primeTowerZeroLagEnergy (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (Real.log (p : ℝ)) ^ 2 / ((p : ℝ) - 1)

noncomputable def primeTowerAutocorrelation (P : Finset ℕ) (h : ℝ) : ℂ :=
  ∑ p ∈ P,
    (((Real.log (p : ℝ)) ^ 2 : ℝ) : ℂ) /
      ((p : ℂ) * Complex.exp
          (Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ)) - 1)

/-- Exact open statement of the admitted finite-prime-tower autocorrelation claim. -/
def finitePrimeTowerAutocorrelationClaim : Prop :=
  ∀ (P : Finset ℕ),
    P.Nonempty →
      (∀ p ∈ P, Nat.Prime p) →
        (∀ h : ℝ,
          Tendsto
            (fun T : ℝ =>
              (1 / T) *
                ∫ t in (0 : ℝ)..T,
                  finitePrimeTowerSum P (t + h) *
                    starRingEnd ℂ (finitePrimeTowerSum P t))
            atTop
            (𝓝 (primeTowerAutocorrelation P h))) ∧
        (∀ h : ℝ,
          ‖primeTowerAutocorrelation P h‖ ≤ primeTowerZeroLagEnergy P) ∧
        (∃ q : ℕ → ℕ,
          (∀ r : ℕ, 0 < q r) ∧
            Tendsto (fun r : ℕ => (q r : ℝ)) atTop atTop ∧
            Tendsto
              (fun r : ℕ => primeTowerAutocorrelation P (q r : ℝ))
              atTop
              (𝓝 (primeTowerZeroLagEnergy P : ℂ))) ∧
        Filter.limsup
            (fun h : ℝ => ‖primeTowerAutocorrelation P h‖)
            atTop =
          primeTowerZeroLagEnergy P ∧
        0 < primeTowerZeroLagEnergy P ∧
        ¬Tendsto
          (fun h : ℝ => ‖primeTowerAutocorrelation P h‖)
          atTop
          (𝓝 0)

end MathlibPlus.Open.Analysis
