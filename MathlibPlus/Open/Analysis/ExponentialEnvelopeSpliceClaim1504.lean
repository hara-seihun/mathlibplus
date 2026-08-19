import Mathlib

namespace MathlibPlus.Open.Analysis.ExponentialEnvelopeSpliceClaim1504

noncomputable def lowConvertedCoefficient (C₁ d₁ d L : ℝ) : ℝ :=
  C₁ * Real.exp ((d - d₁) * Real.sqrt L)

noncomputable def tailConvertedCoefficient (C₂ d₂ d L : ℝ) : ℝ :=
  C₂ * Real.exp (-(d₂ - d) * Real.sqrt L)

/-- The monotonic conversion and endpoint-splice statement of admitted claim 1504. -/
def monotoneExponentialEnvelopeSplice_claim1504 : Prop :=
  ∀ (L₀ C₁ C₂ d₁ d d₂ : ℝ),
    0 < L₀ →
    0 ≤ C₁ →
    d₁ < d →
    0 ≤ C₂ →
    d < d₂ →
    MonotoneOn
      (fun L : ℝ => lowConvertedCoefficient C₁ d₁ d L)
      (Set.Ioc 0 L₀) ∧
    AntitoneOn
      (fun L : ℝ => tailConvertedCoefficient C₂ d₂ d L)
      (Set.Ici L₀) ∧
    ∀ B : ℝ,
      lowConvertedCoefficient C₁ d₁ d L₀ ≤ B →
      tailConvertedCoefficient C₂ d₂ d L₀ ≤ B →
      (∀ L : ℝ, 0 < L → L ≤ L₀ →
        lowConvertedCoefficient C₁ d₁ d L ≤ B) ∧
      (∀ L : ℝ, L₀ ≤ L →
        tailConvertedCoefficient C₂ d₂ d L ≤ B)

end MathlibPlus.Open.Analysis.ExponentialEnvelopeSpliceClaim1504
