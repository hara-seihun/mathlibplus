import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BalancedSegreReserve

noncomputable section

private def signChoice (σ : ℝ) : Prop := σ = 1 ∨ σ = -1

private def phaseX (θ : ℝ) : ℝ := (Real.cos θ) ^ 2

private def phaseG (lam θ σ : ℝ) : ℝ :=
  σ * 3 * Real.sqrt 2 * lam * Real.sin (2 * θ)

private def normalizedReserve (ρ : ℝ) : ℝ := 1 - |ρ|

private def bellFrameQ (lam θ σ t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let x := phaseX θ
  let g := phaseG lam θ σ
  !![
    x / 4 + (t - g / 4), 0, 0, 0;
    0, x / 4 - (t - g / 4), 0, 0;
    0, 0, (4 + x) / 4 + (-t - g / 4), 0;
    0, 0, 0, (4 + x) / 4 - (-t - g / 4)
  ]

private def simpleGaugeUniversallyPSD (lam : ℝ) : Prop :=
  ∀ θ σ : ℝ, signChoice σ →
    Matrix.PosSemidef (bellFrameQ lam θ σ (phaseG lam θ σ / 4))

private def someGaugeUniversallyPSD (lam : ℝ) : Prop :=
  ∀ θ σ : ℝ, signChoice σ →
    ∃ t : ℝ, Matrix.PosSemidef (bellFrameQ lam θ σ t)

/-- Balanced Segre reserve and the threshold loss of the simple null gauge. -/
def claim7784_balancedSegreReserveAndBadGauge : Prop :=
  (∀ θ σ : ℝ, signChoice σ →
    let ρ := phaseG (1 / 2 : ℝ) θ σ / (2 + phaseX θ)
    ρ ^ 2 ≤ (3 / 4 : ℝ) ∧
      (∀ scale : ℝ,
        (scale = phaseX θ ∨ scale = 4 + phaseX θ) →
        scale ≠ 0 →
        normalizedReserve ρ ≥ 1 - Real.sqrt 3 / 2) ∧
      0 < 1 - Real.sqrt 3 / 2) ∧
  (∀ lam : ℝ,
    simpleGaugeUniversallyPSD lam ↔ lam ^ 2 ≤ (5 / 18 : ℝ)) ∧
  (∀ lam : ℝ,
    someGaugeUniversallyPSD lam ↔ lam ^ 2 ≤ (1 / 3 : ℝ)) ∧
  (5 / 18 : ℝ) < 1 / 3

end
end MathlibPlus.Open.ResearchFormalization.BalancedSegreReserve
