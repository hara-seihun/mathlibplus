import Mathlib

namespace MathlibPlus.Open.NewResearch2.LunaBatch.Poisson

noncomputable section

/-- The projective differential in the shifted gauge, with the nonzero and
complex-differentiability domains made explicit. -/
def claim15427_projectiveDifferentialShiftedGauge : Prop :=
  ∀ (L : ℝ) (X B D : ℂ → ℂ),
    (∀ z : ℂ,
      B z = Complex.exp (Complex.I * (L : ℂ) * z) * D z) →
    ∀ z : ℂ,
      X z ≠ 0 → B z ≠ 0 → D z ≠ 0 →
      DifferentiableAt ℂ X z →
      DifferentiableAt ℂ B z →
      DifferentiableAt ℂ D z →
      let m : ℂ := (1 / Complex.I) * deriv B z / B z
      let h : ℂ := (L : ℂ) - Complex.I * deriv X z / X z
      deriv D z / D z = -Complex.I * (L : ℂ) + Complex.I * m ∧
        deriv (fun w : ℂ => -X w / D w) z /
            (-X z / D z) = -Complex.I * (m - h)

end

end MathlibPlus.Open.NewResearch2.LunaBatch.Poisson
