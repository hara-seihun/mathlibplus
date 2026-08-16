import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The gamma--zeta Mellin application, including the normalized logarithmic tilt
and its reflected convolution. -/
def gammaZetaMellinApplication_claim14070 : Prop :=
  let q : ℝ → ℝ := fun x => 1 / x - 1 / (Real.exp x - 1)
  let F : ℂ → ℂ := fun s =>
    ∫ x in Set.Ioi (0 : ℝ),
      Complex.cpow (x : ℂ) (s - (1 : ℂ)) * (q x : ℂ)
  let μ : ℝ → MeasureTheory.Measure ℝ := fun σ =>
    MeasureTheory.Measure.withDensity volume
      (fun y =>
        ENNReal.ofReal
          (Real.exp (σ * y) * q (Real.exp y) /
            (F (σ : ℂ)).re))
  let convolutionPower : MeasureTheory.Measure ℝ → ℕ → MeasureTheory.Measure ℝ :=
    fun ν n =>
      Nat.rec (MeasureTheory.Measure.dirac (0 : ℝ))
        (fun _ acc => MeasureTheory.Measure.conv acc ν) n
  let infinitelyDivisible : MeasureTheory.Measure ℝ → Prop := fun ν =>
    MeasureTheory.IsProbabilityMeasure ν ∧
      ∀ n : ℕ, 0 < n →
        ∃ root : MeasureTheory.Measure ℝ,
          MeasureTheory.IsProbabilityMeasure root ∧
            convolutionPower root n = ν
  ∀ γ : ℝ,
    (let z : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I
     riemannZeta z = 0 ∧
       DifferentiableAt ℂ riemannZeta z ∧
       deriv riemannZeta z ≠ 0 ∧ γ ≠ 0) →
      let z : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I
      Complex.Gamma z ≠ 0 ∧
        F (1 / 2 : ℂ) =
          -Complex.Gamma (1 / 2 : ℂ) * riemannZeta (1 / 2 : ℂ) ∧
        (F (1 / 2 : ℂ)).im = 0 ∧
        0 < (F (1 / 2 : ℂ)).re ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ δ : ℝ, 0 < δ → δ < ε →
            MeasureTheory.IsProbabilityMeasure (μ (1 / 2 + δ)) ∧
              ¬ infinitelyDivisible (μ (1 / 2 + δ)) ∧
              MeasureTheory.IsProbabilityMeasure
                (MeasureTheory.Measure.conv (μ (1 / 2 + δ))
                  (MeasureTheory.Measure.map (fun y : ℝ => -y) (μ (1 / 2 + δ)))) ∧
              ¬ infinitelyDivisible
                (MeasureTheory.Measure.conv (μ (1 / 2 + δ))
                  (MeasureTheory.Measure.map (fun y : ℝ => -y) (μ (1 / 2 + δ))))

/-- The analytic second-derivative spike at a simple boundary zero. -/
def scaledCurvatureLimit_claim14071 : Prop :=
  ∀ (F K : ℂ → ℂ) (a γ : ℝ),
    let ρ : ℂ := (a : ℂ) + (γ : ℂ) * Complex.I
    (γ ≠ 0 ∧
      F ρ = 0 ∧
      DifferentiableAt ℂ F ρ ∧
      deriv F ρ ≠ 0 ∧
      F (a : ℂ) ≠ 0 ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ s : ℂ, s ≠ ρ → ‖s - ρ‖ < r →
          Complex.exp (K s) = F s ∧
            DifferentiableAt ℂ K s ∧
            DifferentiableAt ℂ (deriv K) s) →
      Filter.Tendsto
        (fun δ : ℝ =>
          (δ : ℂ) ^ 2 *
            iteratedDeriv 2 K
              ((a : ℂ) + (δ : ℂ) + (γ : ℂ) * Complex.I))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-1 : ℂ))

end MathlibPlus.Open.Analysis
