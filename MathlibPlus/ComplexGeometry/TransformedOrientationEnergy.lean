import Mathlib

namespace MathlibPlus.ComplexGeometry

/-- Claim 11391: after introducing `κ = cos θ`, `σ = sin θ`,
`H = exp U + exp (-U)`, and `K = exp U - exp (-U)`, the displayed direct
energy has the stated form and the average of the displayed reflected energy
at `(U, Φ)` and `(-U, -Φ)` is the stated `R̄_θ`. -/
theorem transformedOrientationAveragedEnergies_claim11391 (U Φ θ : ℝ) :
    let κ : ℝ := Real.cos θ
    let σ : ℝ := Real.sin θ
    let H : ℝ := Real.exp U + Real.exp (-U)
    let K : ℝ := Real.exp U - Real.exp (-U)
    let direct : ℝ := 4 * (Real.exp U + Real.exp (-U) - 2 * Real.cos Φ)
    let reflected : ℝ → ℝ → ℝ := fun u φ ↦
      4 * (1 + κ ^ 2) * Real.exp u +
        (4 - 2 * κ ^ 2) * Real.exp (-u) +
        4 * Real.sqrt 2 * σ * κ * (2 * Real.exp u - Real.exp (-u)) * Real.sin φ -
        8 * Real.cos φ
    let averaged : ℝ := (reflected U Φ + reflected (-U) (-Φ)) / 2
    direct = 4 * H - 8 * Real.cos Φ ∧
      averaged = (4 + κ ^ 2) * H +
        6 * Real.sqrt 2 * σ * κ * K * Real.sin Φ - 8 * Real.cos Φ := by
  dsimp
  constructor
  · ring
  · simp only [Real.sin_neg, Real.cos_neg, neg_neg]
    ring

end MathlibPlus.ComplexGeometry
