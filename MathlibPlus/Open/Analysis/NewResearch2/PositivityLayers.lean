import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.NewResearch2.PositivityLayers

private def sourceRepresentation (F : ℂ → ℂ) (μ : Measure ℝ) : Prop :=
  Measure.map (fun x : ℝ => -x) μ = μ ∧
    ∀ s : ℂ,
      Integrable (fun x : ℝ => Complex.exp (s * (x : ℂ))) μ ∧
        F s = ∫ x : ℝ, Complex.exp (s * (x : ℂ)) ∂μ

private def sourcePositive (F : ℂ → ℂ) : Prop :=
  ∃ μ : Measure ℝ, sourceRepresentation F μ

private def boundaryPositive (F : ℂ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    let q : ℂ :=
      ∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          F (Complex.I * ((t i - t j : ℝ) : ℂ))
    0 ≤ q.re ∧ q.im = 0

/-- Claim 4877: source positivity is the bilateral Laplace transform of a
positive symmetric measure. -/
def sourcePositivityCone_claim4877 (F : ℂ → ℂ) : Prop :=
  sourcePositive F

/-- Claim 4878: boundary positivity is positive semidefiniteness of every
finite Bochner kernel quadratic form built from the boundary values. -/
def boundaryPositivityCone_claim4878 (F : ℂ → ℂ) : Prop :=
  boundaryPositive F

/-- Claim 4881: a positive symmetric source representation passes to the
boundary kernel through the Bochner positive-definiteness statement. -/
def bochnerPassageFromSource_claim4881 : Prop :=
  ∀ (F : ℂ → ℂ) (μ : Measure ℝ),
    sourceRepresentation F μ → boundaryPositive F

end MathlibPlus.Open.Analysis.NewResearch2.PositivityLayers
