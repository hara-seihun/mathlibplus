import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffedc

noncomputable section

/-- The phase factor used by a fixed supporting phase. -/
def phaseFactor (θ : ℝ) : ℂ := Complex.exp (-(θ : ℂ) * Complex.I)

/-- Claim 11367: the fixed-phase jet has only the real logarithmic curvature,
while the moving modulus has the additional squared transverse logarithmic jet. -/
def fixed_supporting_phase_misses_positive_square : Prop :=
  (∀ (F : ℝ → ℂ) (σ₀ : ℝ),
      F σ₀ ≠ 0 →
      DifferentiableAt ℝ F σ₀ →
      DifferentiableAt ℝ (deriv F) σ₀ →
      DifferentiableAt ℝ (fun σ => ‖F σ‖) σ₀ →
      DifferentiableAt ℝ (deriv (fun σ => ‖F σ‖)) σ₀ →
        let θ := Complex.arg (F σ₀)
        let Y : ℝ → ℝ := fun σ => (phaseFactor θ * F σ).re
        let Y₀ : ℝ := Y σ₀
        let Y₂ : ℝ := deriv (deriv Y) σ₀
        let F₁ := deriv F σ₀
        let F₂ := deriv (deriv F) σ₀
        Y₀ = ‖F σ₀‖ ∧
          Y₂ / Y₀ = (F₂ / F σ₀).re ∧
          (deriv (deriv (fun σ => ‖F σ‖)) σ₀) / ‖F σ₀‖ =
            (F₂ / F σ₀).re + ((F₁ / F σ₀).im) ^ 2 ∧
          0 ≤ ((F₁ / F σ₀).im) ^ 2) ∧
    (∃ (F : ℝ → ℂ) (σ₀ : ℝ),
      F = (fun σ : ℝ => Complex.exp (Complex.I * (σ : ℂ))) ∧
      σ₀ = 0 ∧ F σ₀ ≠ 0 ∧
      ((deriv F σ₀ / F σ₀).im) ^ 2 > 0)

/-- The two-by-two Hermitian matrix with real diagonal and upper-right entry `z`. -/
def hermitianTwoByTwo (P H : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = (0 : Fin 2) then
      if j = (0 : Fin 2) then (P : ℂ) else z
    else if j = (0 : Fin 2) then starRingEnd ℂ z else (H : ℂ)

/-- Claim 11375: an ordinary Hermitian two-by-two determinant carries the
phase-current term with the opposite sign, so it cannot equal `PH+j²` for
nonzero `j`. -/
def ordinary_hermitian_gram_has_wrong_sign : Prop :=
  ∀ (P H j : ℝ),
    Matrix.det (hermitianTwoByTwo P H (Complex.I * (j : ℂ))) =
        ((P * H - j ^ 2 : ℝ) : ℂ) ∧
      (∀ z : ℂ,
        Matrix.IsHermitian (hermitianTwoByTwo P H z) ∧
          Matrix.det (hermitianTwoByTwo P H z) =
            ((P * H : ℝ) : ℂ) - (Complex.normSq z : ℂ)) ∧
      (j ≠ 0 →
        ¬ ∃ z : ℂ,
          Matrix.det (hermitianTwoByTwo P H z) =
            ((P * H + j ^ 2 : ℝ) : ℂ))

end

end MathlibPlus.Open.ResearchFormalization.Batch019ffedc
