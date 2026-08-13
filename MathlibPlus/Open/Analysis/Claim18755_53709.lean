import MathlibPlus.Basic

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Exact finite exponential-polynomial faithfulness statement from claim 18755.
The accumulation point is represented explicitly by membership in the closure of
`S` after removing that point. -/
def finiteLaplaceFaithfulness18755 : Prop :=
  ∀ (m : ℕ) (t c : Fin m → ℝ) (S : Set ℂ) (z₀ : ℂ),
    Function.Injective t →
    z₀ ∈ closure (S \ {z₀}) →
    (∀ z ∈ S, ∑ j : Fin m, (c j : ℂ) * Complex.exp (-z * (t j : ℂ)) = 0) →
    ∀ j : Fin m, c j = 0

/-- Exact Fourier convention used for the nonzero-frequency obstruction in claim
53709.  The hypotheses use the natural `L¹` and almost-everywhere positivity
formulation; the transform is the unnormalised `exp (-I * Δ * x)` integral. -/
def nonnegativeL1FourierNotOne53709 : Prop :=
  ∀ (K : ℝ → ℝ),
    Integrable K ∧
    (0 ≤ᵐ[volume] K) ∧
    (∫ x, K x = 1) →
    ∀ Δ : ℝ, Δ ≠ 0 →
      (∫ x : ℝ,
          (K x : ℂ) * Complex.exp (-Complex.I * (Δ : ℂ) * (x : ℂ))) ≠ 1

end MathlibPlus.Open.Analysis
