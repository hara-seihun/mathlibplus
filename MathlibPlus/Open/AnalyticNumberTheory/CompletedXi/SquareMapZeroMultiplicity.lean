import Mathlib

/-!
# The square-map image of nontrivial zeta zeros

Statement-fidelity formalization of admitted claim 450.  Multiplicity is expressed by
local factorization: an analytic zero has exact multiplicity `n` when it is locally
`(z-z₀)^n` times a continuous nonvanishing factor.  The final equivalence says that
pullback along `w ↦ w²` introduces no extra multiplicity away from its branch point.
-/

open Filter

namespace MathlibPlus.Open.AnalyticNumberTheory.CompletedXi

/-- Every nontrivial zeta zero maps under `ρ ↦ (ρ - 1/2)²` to the corresponding
zero of the square-root xi transform.  The functional-equation partner has the same
image, and local zero multiplicity is unchanged by the square map. -/
def squareMapZeroMultiplicity : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let HasZeroMultiplicity : (ℂ → ℂ) → ℂ → ℕ → Prop := fun f z₀ n =>
    ∃ g : ℂ → ℂ,
      ContinuousAt g z₀ ∧ g z₀ ≠ 0 ∧
        ∀ᶠ z in nhds z₀, f z = (z - z₀) ^ n * g z
  ∃ xi₁ : ℂ → ℂ,
    (∀ w : ℂ, xi₁ (w ^ 2) = xi ((1 / 2 : ℂ) + w)) ∧
    ∀ ρ : ℂ,
      riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 →
      let w := ρ - (1 / 2 : ℂ)
      let zρ := w ^ 2
      xi₁ zρ = 0 ∧
      riemannZeta (1 - ρ) = 0 ∧
      ((1 - ρ) - (1 / 2 : ℂ)) ^ 2 = zρ ∧
      w ≠ 0 ∧
      ∀ n : ℕ, HasZeroMultiplicity xi₁ zρ n ↔
        HasZeroMultiplicity (fun z => xi ((1 / 2 : ℂ) + z)) w n

end MathlibPlus.Open.AnalyticNumberTheory.CompletedXi
