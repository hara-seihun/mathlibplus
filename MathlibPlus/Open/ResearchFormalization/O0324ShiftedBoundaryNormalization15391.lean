import MathlibPlus.Algebra.Claim15385
import MathlibPlus.Open.ResearchFormalization.Claim15392

namespace MathlibPlus.Open.ResearchFormalization.O0324ShiftedBoundaryNormalization15391

noncomputable section

/-- The exponentially shifted boundary transform in Claim 15391. -/
noncomputable def shiftedBoundaryTransform15391
    (L : ℝ) (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (L : ℂ) * z) *
    MathlibPlus.Open.ResearchFormalization.O0324.boundaryTransform μ z

/-- The branch-independent logarithmic differential of the projective
shadow-defect coordinate. -/
noncomputable def projectiveLogDerivative15391
    (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun w => -X w / D w) z / (-X z / D z)

/-- Claim 15391: the finite-measure first-moment quotient gives the shifted
boundary logarithmic derivative, and the projective logarithmic differential is
its defect from the normalized derivative of X. -/
def claim15391 : Prop :=
  ∀ (X : ℝ → ℂ → ℂ)
    (μ : ℝ → MeasureTheory.ComplexMeasure ℝ),
    (∀ L : ℝ, Differentiable ℂ (X L)) →
      ∀ (L : ℝ) (z : ℂ),
        MathlibPlus.Open.ResearchFormalization.O0324.finiteExpWeightedFirstMoment
            (μ L) z.im →
          MathlibPlus.Open.ResearchFormalization.O0324.boundaryTransform
              (μ L) z ≠ 0 →
            X L z ≠ 0 →
              shiftedBoundaryTransform15391 L (μ L) z ≠ 0 →
                let m : ℂ :=
                  MathlibPlus.Open.ResearchFormalization.O0324.effectiveDepth
                    (μ L) z
                let h : ℂ :=
                  (L : ℂ) - Complex.I * deriv (X L) z / X L z
                let Δ : ℂ := m - h
                deriv (shiftedBoundaryTransform15391 L (μ L)) z /
                      shiftedBoundaryTransform15391 L (μ L) z =
                    -Complex.I * (L : ℂ) + Complex.I * m ∧
                  projectiveLogDerivative15391
                      (X L) (shiftedBoundaryTransform15391 L (μ L)) z =
                    -Complex.I * Δ

end

end MathlibPlus.Open.ResearchFormalization.O0324ShiftedBoundaryNormalization15391
