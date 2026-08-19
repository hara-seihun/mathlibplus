import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchO0078

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078

noncomputable def primitiveG6 (u : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
    ∑ n ∈ Finset.Icc 1 (Nat.floor (Real.exp u)),
      (((n : ℝ) / Real.exp u) ^ 2) *
        (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4

noncomputable def primitiveLaplace (s : ℂ) : ℂ :=
  ∫ u,
    Complex.exp (-s * (u : ℂ)) * (primitiveG6 u : ℂ) ∂nonnegativeVolume

noncomputable def primitiveTransform (s : ℂ) : ℂ :=
  32 * riemannZeta s /
    ((s + 2) * (s + 4) * (s + 6) * (s + 8) * (s + 10))

noncomputable def shiftedPrimitiveMoment0 (σ t : ℝ) : ℂ :=
  primitiveTransform (complexLine σ t)

noncomputable def shiftedPrimitiveMoment1 (σ t : ℝ) : ℂ :=
  -deriv primitiveTransform (complexLine σ t) +
    (q6 σ t : ℂ) * primitiveTransform (complexLine σ t)

noncomputable def shiftedPrimitiveMoment2 (σ t : ℝ) : ℂ :=
  deriv (deriv primitiveTransform) (complexLine σ t) -
    2 * (q6 σ t : ℂ) * deriv primitiveTransform (complexLine σ t) +
      (q6 σ t : ℂ) ^ 2 * primitiveTransform (complexLine σ t)

/-- The admitted first three Darboux moment coordinates, with the actual
m=6 lattice primitive, its convergent Laplace carrier, analytic continuation,
discrepancy carrier, and gamma phase shift exposed in the definitions. -/
def claim12134 : Prop :=
  (∀ s : ℂ, 1 < s.re → primitiveTransform s = primitiveLaplace s) ∧
  (∀ (σ t : ℝ),
    (1 / 2 : ℝ) < σ → σ < 1 →
      let s : ℂ := complexLine σ t
      let p : ℂ := s - 1
      let N₀ : ℂ := shiftedPrimitiveMoment0 σ t
      let N₁ : ℂ := shiftedPrimitiveMoment1 σ t
      let N₂ : ℂ := shiftedPrimitiveMoment2 σ t
      let M₀ : ℂ := moment σ t 0
      let M₁ : ℂ := moment σ t 1
      let M₂ : ℂ := moment σ t 2
      M₀ = p * N₀ ∧
        M₁ = p * N₁ - N₀ ∧
        M₂ = p * N₂ - 2 * N₁)

end MathlibPlus.Open.ResearchFormalization.BatchO0078
