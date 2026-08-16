import Mathlib
import Mathlib.MeasureTheory.Measure.Complex

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.O0324

noncomputable section

/-- The finite complex Borel-measure hypothesis needed by the charge integrals:
finite total variation and the exponentially weighted zeroth and first moments. -/
def finiteExpWeightedFirstMoment
    (μ : MeasureTheory.ComplexMeasure ℝ) (y : ℝ) : Prop :=
  IsFiniteMeasure (VectorMeasure.variation μ) ∧
    Integrable (fun τ : ℝ => Real.exp (-y * τ))
      (VectorMeasure.variation μ) ∧
    Integrable (fun τ : ℝ => |τ| * Real.exp (-y * τ))
      (VectorMeasure.variation μ)

/-- The Fourier--Laplace carrier `B_L(z)=∫ exp(i z τ) dμ_L(τ)`. -/
noncomputable def boundaryTransform
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ τ : ℝ,
    Complex.exp (Complex.I * z * (τ : ℂ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- The first-moment Fourier--Laplace numerator. -/
noncomputable def firstMomentTransform
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ τ : ℝ,
    (τ : ℂ) * Complex.exp (Complex.I * z * (τ : ℂ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- The effective depth quotient `m_L(z)`. -/
noncomputable def effectiveDepth
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  firstMomentTransform μ z / boundaryTransform μ z

/-- The exact endpoint-window absolute charge, divided by the nonzero carrier. -/
noncomputable def innerCharge
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) (r : ℝ) : ℝ :=
  (∫ τ : ℝ,
      Real.exp (-z.im * τ) ∂
        ((VectorMeasure.variation μ).restrict {τ : ℝ | |τ| ≤ r})) /
    ‖boundaryTransform μ z‖

/-- The normalized tail charge outside the endpoint window. -/
noncomputable def outerCharge
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) (L r : ℝ) : ℝ :=
  (∫ τ : ℝ,
      |τ| * Real.exp (-z.im * τ) ∂
        ((VectorMeasure.variation μ).restrict {τ : ℝ | r < |τ|})) /
    (L * ‖boundaryTransform μ z‖)

/-- Claim 15392.  The measure is a genuine finite complex Borel measure with
its required exponentially weighted first moment; no unconstrained finite
measure or arbitrary transform callback is used. -/
def finiteMeasureDepthInequality_claim15392 : Prop :=
  ∀ (μ : ℝ → MeasureTheory.ComplexMeasure ℝ)
    (L r x y : ℝ),
    0 < r → r < L →
    finiteExpWeightedFirstMoment (μ L) y →
    boundaryTransform (μ L) ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 →
    let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
    ‖effectiveDepth (μ L) z‖ / L ≤
      (r / L) * innerCharge (μ L) z r +
        outerCharge (μ L) z L r

end
end MathlibPlus.Open.ResearchFormalization.O0324
