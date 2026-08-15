import Mathlib

open scoped BigOperators Interval
open MeasureTheory

namespace MathlibPlus.Open.FormalizationBatch

/-- Exact fiberwise periodic least-squares minimum from admitted Claim 9408. -/
def exact_fiberwise_periodic_least_squares_minimum_9408 : Prop :=
  ∀ q : ℤ, (2 : ℤ) ≤ q →
    let qR : ℝ := (q : ℝ)
    let L : ℝ := Real.log qR
    let r : ℝ := Real.rpow qR (-1 / 2 : ℝ)
    let T : ℝ := 2 * Real.pi / L
    let μ' : ℝ → ℝ := fun t => 1 / (2 * Real.pi * (1 / 4 + t ^ 2))
    let μ : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (μ' t))
    let Φ : ℂ → ℂ := fun z =>
      Complex.exp (-((L : ℂ) / 2) * ((1 + z) / (1 - z)))
    let Z : ℂ → ℂ := fun z => z * riemannZeta (1 / (1 - z))
    let H : ℂ → ℂ := fun z =>
      Z z * (1 - (r : ℂ) * Φ z) / ((1 : ℂ) - (r : ℂ) ^ 2)
    let Hq : ℝ → ℂ := fun t =>
      H (1 - 1 / ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
    let δ : ℝ :=
      sInf {v : ℝ | ∃ g : ℝ → ℂ,
        Measurable g ∧
          (∀ t : ℝ, g (t + T) = g t) ∧
            v = ∫ t : ℝ, ‖g t * Hq t - 1‖ ^ 2 ∂μ}
    let A : ℝ → ℝ := fun x =>
      ∑' k : ℤ,
        μ' (x + (k : ℝ) * T) * ‖Hq (x + (k : ℝ) * T)‖ ^ 2
    let C : ℝ → ℂ := fun x =>
      ∑' k : ℤ,
        (μ' (x + (k : ℝ) * T) : ℂ) *
          star (Hq (x + (k : ℝ) * T))
    let D : ℝ → ℝ := fun x =>
      ∑' k : ℤ, μ' (x + (k : ℝ) * T)
    δ = ∫ x in (0 : ℝ)..T, D x - ‖C x‖ ^ 2 / A x

/-- Intrinsic Dini--Laguerre phase derivative from admitted Claim 9428. -/
def intrinsic_dini_laguerre_phase_derivative_9428 : Prop :=
  ∀ (Y Y_u Y_uu : ℝ → ℝ),
    (∀ u : ℝ, HasDerivAt Y (Y_u u) u) →
      (∀ u : ℝ, HasDerivAt Y_u (Y_uu u) u) →
        let W : ℝ → ℂ := fun u => (Y u : ℂ) + (Y_u u : ℂ) * Complex.I
        let L_Y : ℝ → ℝ := fun u => Y_u u ^ 2 - Y u * Y_uu u
        ∀ u : ℝ,
          0 < Y u ^ 2 + Y_u u ^ 2 →
            deriv (fun v : ℝ => Complex.arg (W v)) u =
                (Y u * Y_uu u - Y_u u ^ 2) / (Y u ^ 2 + Y_u u ^ 2) ∧
              (Y u * Y_uu u - Y_u u ^ 2) / (Y u ^ 2 + Y_u u ^ 2) =
                -L_Y u / (Y u ^ 2 + Y_u u ^ 2)

end MathlibPlus.Open.FormalizationBatch
