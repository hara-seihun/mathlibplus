import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Resonance-safe positive-density level set for a nonempty nearest phase
shell.  The radius/point representation, injectivity, nontriviality, and
involution encode the source shell data; no phase-independence hypothesis is
introduced. -/
def resonanceSafePositiveLevelSet_claim3441 : Prop :=
  ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
    (R : ℝ) (z : ι → ℂ) (m : ι → ℕ) (θ : ι → ℝ) (τ : ι → ι),
    0 < R →
    Nonempty ι →
    (∀ ρ, z ρ = (R : ℂ) * Complex.exp (Complex.I * (θ ρ : ℂ))) →
    (Function.Injective (fun ρ => Complex.exp (Complex.I * (θ ρ : ℂ)))) →
    (∀ ρ, Complex.exp (Complex.I * (θ ρ : ℂ)) ≠ 1) →
    Function.Involutive τ →
    (∀ ρ, 0 < m ρ) →
    (∀ ρ, m (τ ρ) = m ρ) →
    (∀ ρ,
      Complex.exp (Complex.I * (θ (τ ρ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * (θ ρ : ℂ)))) →
    let P : ℕ → ℂ := fun n =>
      ∑ ρ, (m ρ : ℂ) *
        Complex.exp (-((n : ℂ) * Complex.I * (θ ρ : ℂ)))
    (∀ n, (P n).im = 0) ∧
      ∃ δ d : ℝ,
        0 < δ ∧ 0 < d ∧
          Filter.Tendsto
            (fun N : ℕ =>
              ((Finset.filter (fun n : ℕ => δ < (P n).re)
                (Finset.Icc 1 N)).card : ℝ) / (N : ℝ))
            Filter.atTop (nhds d)

end MathlibPlus.Open.Analysis
