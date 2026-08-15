import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a00396_e154_7076_927f_0d48a4d48a4e

noncomputable section

/-- The Gamma ratio appearing in the zero-lag determinant claim. -/
def gammaRatio7813 (a τ : ℝ) : ℂ :=
  Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I) / Complex.Gamma (a : ℂ)

/-- Positive-real-base complex powers used by the dyadic Clifford factor. -/
def dyadicPow7813 (w : ℂ) : ℂ :=
  Complex.cpow (2 : ℂ) w

/-- The zero-lag Schur-completed two-by-two kernel supplied by the packet. -/
def kTildeZero7813 (a τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I
  let gammaMinus : ℂ := Complex.Gamma ((a : ℂ) - (τ : ℂ) * Complex.I) / Complex.Gamma (a : ℂ)
  let gammaPlus : ℂ := gammaRatio7813 a τ
  !![1, dyadicPow7813 (s - 1) * gammaMinus;
     dyadicPow7813 (-s) * gammaPlus, 1]

/-- Uniform zero-lag determinant reserve, retained as an open proposition. -/
def claim7813 : Prop :=
  ∀ (a τ : ℝ), 0 < a →
    let γ : ℂ := gammaRatio7813 a τ
    let determinant : ℂ := Matrix.det (kTildeZero7813 a τ)
    let reserve : ℝ := 1 - (1 / 2 : ℝ) * ‖γ‖ ^ 2
    determinant = (reserve : ℂ) ∧
      reserve ≥ (1 / 2 : ℝ) ∧
      (τ = 0 → reserve = (1 / 2 : ℝ)) ∧
      (τ ≠ 0 → reserve > (1 / 2 : ℝ))

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a00396_e154_7076_927f_0d48a4d48a4e
