import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CenteredHessian

noncomputable def boundaryHessian (jpp jp j : ℂ) (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![jpp, jp; jp, j + (a : ℂ)]

def centeredDeterminantReserve : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (a : Ω → ℝ) (V_N : ℝ) (jpp jp j : ℂ),
    Measurable a →
    MeasureTheory.Integrable (fun ω => (a ω : ℂ)) μ →
    MeasureTheory.Integrable (fun ω => ((a ω : ℂ) ^ 2)) μ →
    (∫ ω, a ω ∂μ) = 0 →
    (∫ ω, (a ω) ^ 2 ∂μ) = V_N →
    (∫ ω, Matrix.det (boundaryHessian jpp jp j (a ω)) ∂μ =
        jpp * j - jp * jp) ∧
      (∫ ω, ‖Matrix.det (boundaryHessian jpp jp j (a ω)) -
          (jpp * j - jp * jp)‖ ^ 2 ∂μ =
        V_N * ‖jpp‖ ^ 2)

end MathlibPlus.Open.ResearchFormalization.CenteredHessian
