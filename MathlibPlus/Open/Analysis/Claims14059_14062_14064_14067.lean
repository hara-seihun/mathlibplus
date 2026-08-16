import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory Asymptotics Filter

namespace MathlibPlus.Open.Analysis

/-- Claim 14059: endpoint asymptotics and the exact Mellin convergence strip. -/
def claim14059 : Prop :=
  let q : ℝ → ℝ := fun x => 1 / x - 1 / (Real.exp x - 1)
  IsBigO (nhdsWithin (0 : ℝ) (Ioi 0))
      (fun x => q x - (1 / 2 : ℝ)) (fun x => x) ∧
    IsBigO atTop (fun x => q x - 1 / x) (fun x => Real.exp (-x)) ∧
    ∀ s : ℂ,
      IntegrableOn
        (fun x : ℝ =>
          ‖Complex.cpow (x : ℂ) (s - 1) * (q x : ℂ)‖)
        (Ioi 0) volume ↔
        0 < s.re ∧ s.re < 1

/-- Claim 14062: the logarithmic-tilt characteristic function and its zeros. -/
def claim14062 : Prop :=
  let q : ℝ → ℝ := fun x => 1 / x - 1 / (Real.exp x - 1)
  let F : ℂ → ℂ := fun s =>
    ∫ x in Ioi (0 : ℝ), Complex.cpow (x : ℂ) (s - 1) * (q x : ℂ)
  let Freal : ℝ → ℝ := fun σ => (F (σ : ℂ)).re
  let density : ℝ → ℝ → ENNReal := fun σ y =>
    ENNReal.ofReal
      (Real.exp (σ * y) * q (Real.exp y) / Freal σ)
  let μ : ℝ → Measure ℝ := fun σ => volume.withDensity (density σ)
  (∀ σ : ℝ, 0 < σ → σ < 1 →
      0 < Freal σ ∧ (F (σ : ℂ)).im = 0 ∧ F (σ : ℂ) ≠ 0 ∧
        Complex.Gamma (σ : ℂ) * riemannZeta (σ : ℂ) ≠ 0 ∧ μ σ univ = 1) ∧
    (∀ z : ℂ, Complex.Gamma z ≠ 0) ∧
    ∀ σ : ℝ, 0 < σ → σ < 1 →
      ∀ t : ℝ,
        (∫ y, Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) ∂(μ σ)) =
          F ((σ : ℂ) + (t : ℂ) * Complex.I) / F (σ : ℂ) ∧
        F ((σ : ℂ) + (t : ℂ) * Complex.I) / F (σ : ℂ) =
          (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) *
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) /
            (Complex.Gamma (σ : ℂ) * riemannZeta (σ : ℂ)) ∧
        (F ((σ : ℂ) + (t : ℂ) * Complex.I) / F (σ : ℂ) = 0 ↔
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) = 0)

/-- Claim 14064: positive definiteness gives the direct two-point bound. -/
def claim14064 : Prop :=
  ∀ (σ : ℝ) (K : ℂ → ℂ),
    let H : ℝ → ℂ := fun t =>
      deriv (deriv K) ((σ : ℂ) + (t : ℂ) * Complex.I)
    let positiveDefinite : Prop :=
      ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
        let S : ℂ := ∑ i, ∑ j,
          star (c i) * c j * H (x i - x j)
        S.im = 0 ∧ 0 ≤ S.re
    positiveDefinite →
      (H 0).im = 0 ∧ ∀ t : ℝ, ‖H t‖ ≤ (H 0).re

/-- Claim 14067: a simple boundary zero produces a negative inverse-square spike. -/
def claim14067 : Prop :=
  let F : ℂ → ℂ := fun s => -Complex.Gamma s * riemannZeta s
  ∀ (a γ : ℝ) (ρ : ℂ),
    ρ = (a : ℂ) + (γ : ℂ) * Complex.I →
    γ ≠ 0 →
    AnalyticAt ℂ F ρ → F ρ = 0 → deriv F ρ ≠ 0 →
    F (a : ℂ) ≠ 0 →
    ∀ (r : ℝ) (G L K : ℂ → ℂ),
      0 < r →
      AnalyticOn ℂ G (Metric.ball ρ r) → G ρ ≠ 0 →
      (∀ s ∈ Metric.ball ρ r, F s = (s - ρ) * G s) →
      AnalyticOn ℂ L (Metric.ball ρ r) →
      (∀ s ∈ Metric.ball ρ r, Complex.exp (L s) = G s) →
      AnalyticOn ℂ K (Metric.ball ρ r \ {ρ}) →
      (∀ s ∈ Metric.ball ρ r \ {ρ}, Complex.exp (K s) = F s) →
      (∀ s ∈ Metric.ball ρ r \ {ρ},
        deriv (deriv K) s =
          -((s - ρ)⁻¹) ^ 2 + deriv (deriv L) s) ∧
      IsBigO (nhdsWithin (0 : ℝ) (Ioi 0))
        (fun δ : ℝ =>
          deriv (deriv K)
              ((a : ℂ) + (δ : ℂ) + (γ : ℂ) * Complex.I) +
            (((δ : ℂ)⁻¹) ^ 2))
        (fun _ : ℝ => (1 : ℂ))

end MathlibPlus.Open.Analysis
