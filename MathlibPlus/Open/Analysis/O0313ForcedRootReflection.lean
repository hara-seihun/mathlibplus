import Mathlib

open scoped Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis.O0313ForcedRootReflection

noncomputable section

/-- The standard disk meaning of an inner function: bounded holomorphic in the
open disk and with unimodular radial boundary values almost everywhere. -/
def innerOnUnitDisk (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) ∧
    (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → ‖F z‖ ≤ 1) ∧
    (∀ᵐ θ : ℝ ∂MeasureTheory.volume,
      ∃ ℓ : ℂ,
        Tendsto
          (fun ρ : ℝ =>
            F ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (𝓝[<] (1 : ℝ)) (𝓝 ℓ) ∧
          ‖ℓ‖ = 1)

/-- The geometric multiplier `q^(-s)` and its disk coordinate. -/
noncomputable def geometricPower (q : ℤ) (s : ℂ) : ℂ :=
  let L : ℝ := Real.log (q : ℝ)
  Complex.exp (-s * (L : ℂ))

noncomputable def geometricPhi (q : ℤ) (z : ℂ) : ℂ :=
  let L : ℝ := Real.log (q : ℝ)
  Complex.exp (-((L : ℂ) / 2) * ((1 + z) / (1 - z)))

/-- The pole-cancellation and central-value statement for a commensurate
polynomial multiplier. -/
def forcedRootPoleCancellation : Prop :=
  ∀ (q : ℤ), 2 ≤ q →
    ∀ P : Polynomial ℂ,
      let L : ℝ := Real.log (q : ℝ)
      let r : ℝ := Real.exp (-L / 2)
      let rC : ℂ := (r : ℂ)
      let A : ℂ → ℂ := fun s => Polynomial.eval (geometricPower q s) P
      let center : ℂ :=
        -(L : ℂ) * rC ^ 2 * Polynomial.eval (rC ^ 2) P.derivative
      let F : ℂ → ℂ := fun s =>
        if s = 1 then center else A s * riemannZeta s
      (Polynomial.eval ((q : ℂ)⁻¹) P = 0 ↔
          Polynomial.eval (rC ^ 2) P = 0) ∧
        (Polynomial.eval (rC ^ 2) P = 0 ↔
          DifferentiableAt ℂ F 1) ∧
        (Polynomial.eval (rC ^ 2) P = 0 →
          (Polynomial.eval (rC ^ 2) P.derivative ≠ 0 ↔ F 1 ≠ 0)) ∧
        geometricPower q 1 = rC ^ 2 ∧
        (Polynomial.eval (rC ^ 2) P = 0 →
          ∀ s : ℂ, geometricPower q s = rC ^ 2 →
            s = 1 ∨ (s ≠ 1 ∧ A s = 0))

/-- The one-root reflection across the critical circle. -/
def oneRootCriticalCircleReflection : Prop :=
  ∀ (q : ℤ), 2 ≤ q →
    ∀ α : ℂ, 0 < ‖α‖ →
      let L : ℝ := Real.log (q : ℝ)
      let r : ℝ := Real.exp (-L / 2)
      let rC : ℂ := (r : ℂ)
      ‖α‖ < r →
        let a : ℂ := α / rC
        let b : ℂ → ℂ := fun u => (u - a) / (1 - star a * u)
        let αstar : ℂ := rC ^ 2 / star α
        innerOnUnitDisk (fun z : ℂ => b (geometricPhi q z)) ∧
          (∀ z : ℂ, ‖z‖ < 1 →
            geometricPhi q z - a =
              b (geometricPhi q z) *
                (1 - star a * geometricPhi q z)) ∧
          (∀ w : ℂ, ‖w‖ = r →
            ‖w - α‖ =
              ‖rC * (1 - star α * w / rC ^ 2)‖) ∧
          (∀ w : ℂ,
            rC * (1 - star α * w / rC ^ 2) = 0 ↔ w = αstar) ∧
          r < ‖αstar‖

/-- The forced progression split into its central and noncentral inner
factors, including the center mass. -/
def forcedProgressionSplit : Prop :=
  ∀ (q : ℤ), 2 ≤ q →
    let L : ℝ := Real.log (q : ℝ)
    let r : ℝ := Real.exp (-L / 2)
    let rC : ℂ := (r : ℂ)
    let b : ℂ → ℂ := fun u => (u - rC) / (1 - rC * u)
    ∃ J : ℂ → ℂ,
      innerOnUnitDisk J ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        geometricPhi q z - rC =
          b (geometricPhi q z) * (1 - rC * geometricPhi q z)) ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        b (geometricPhi q z) = z * J z) ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        (J z = 0 ↔ z ≠ 0 ∧ geometricPhi q z = rC)) ∧
      -Real.log ‖J 0‖ =
          Real.log ((1 - r ^ 2) / (L * r)) ∧
      Real.log ((1 - r ^ 2) / (L * r)) =
        Real.log (Real.sinh (L / 2) / (L / 2))

end

end MathlibPlus.Open.Analysis.O0313ForcedRootReflection
