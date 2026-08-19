import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0757

noncomputable def pairedEndpointCeiling (S δ : ℝ) : ℝ :=
  4 * S + 4 * δ + δ ^ 2 -
    27 * Real.rpow (3 / (δ * (4 + δ))) (1 / 27 : ℝ)

/-- The paired-endpoint AM--GM ceiling, with the monic integral endpoint
    carrier and the exact 27-interior-root setup retained. -/
def claim24496 : Prop :=
  ∀ (ell : Polynomial ℤ) (δ : ℝ) (α : Fin 27 → ℝ),
    ell.Monic →
    ell.natDegree = 28 →
    0 < δ →
    (∀ i : Fin 27, 0 < α i ∧ α i < 4) →
    0 < -ell.eval (2 : ℤ) →
    0 < ell.eval (-2 : ℤ) →
    ((-ell.eval (2 : ℤ) + ell.eval (-2 : ℤ)) % 4 = 0) →
    (-ell.eval (2 : ℤ)) * ell.eval (-2 : ℤ) =
      δ * (4 + δ) * ∏ i : Fin 27, α i * (4 - α i) →
    let S : ℝ := (4 + δ) + ∑ i : Fin 27, α i
    let p₂ : ℝ := (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2
    p₂ ≤ pairedEndpointCeiling S δ ∧
      (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ < δ₂ →
        pairedEndpointCeiling S δ₁ < pairedEndpointCeiling S δ₂)

end MathlibPlus.Open.ResearchFormalization.R0757
