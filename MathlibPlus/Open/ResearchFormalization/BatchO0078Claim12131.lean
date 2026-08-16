import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078

/-- Split-adjoint realization of the three shifted moments. -/
def claim12131 : Prop :=
  ∀ (θ : ℝ) (q' : ℝ) (M₀ M₁ M₂ Y Y_t Y_tt : ℂ),
    Y = Complex.exp (Complex.I * (θ : ℂ)) * M₀ →
    Y_t = Complex.I * Complex.exp (Complex.I * (θ : ℂ)) * M₁ →
    Y_tt = Complex.exp (Complex.I * (θ : ℂ)) *
      (-M₂ + Complex.I * (q' : ℂ) * M₀) →
      let X : Matrix (Fin 2) (Fin 2) ℂ := !![M₁, M₀; M₂, -M₁]
      let conjugateX : Matrix (Fin 2) (Fin 2) ℂ :=
        fun i j => starRingEnd ℂ (X i j)
      let D_t_Y : ℝ := Complex.normSq Y_t - (Y_tt * starRingEnd ℂ Y).re
      ((Matrix.trace X = 0) ∧
        (D_t_Y = Complex.normSq M₁ + (M₂ * starRingEnd ℂ M₀).re) ∧
        ((D_t_Y : ℂ) = (1 / 2 : ℂ) * Matrix.trace (X * conjugateX))) ∧
        ∀ (ρ : ℝ), 0 < ρ →
          let s : ℂ := (Real.sqrt ρ : ℂ)
          let A : Matrix (Fin 2) (Fin 2) ℂ := !![s, 0; 0, s⁻¹]
          let Ainv : Matrix (Fin 2) (Fin 2) ℂ := !![s⁻¹, 0; 0, s]
          let conjugated : Matrix (Fin 2) (Fin 2) ℂ := A * X * Ainv
          (A * Ainv = 1 ∧ Ainv * A = 1) ∧
            conjugated = !![M₁, (ρ : ℂ) * M₀; (ρ : ℂ)⁻¹ * M₂, -M₁]

end MathlibPlus.Open.ResearchFormalization.BatchO0078
