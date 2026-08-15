import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def laguerreCurvature (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖deriv f t‖ ^ 2 -
    Complex.re (deriv (deriv f) t * star (f t))

noncomputable def horizontalLaguerreGaugeIdentity : Prop :=
  ∀ (r θ : ℝ → ℝ) (H C F Y : ℝ → ℂ),
    ContDiff ℝ 2 r →
    ContDiff ℝ 2 θ →
    ContDiff ℝ 2 H →
    ContDiff ℝ 2 C →
    ContDiff ℝ 2 F →
    ContDiff ℝ 2 Y →
    (∀ t, 0 < r t) →
    (∀ t, C t = (r t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) →
    (∀ t, Y t = Complex.exp (Complex.I * (θ t : ℂ)) * H t) →
    (∀ t, F t = C t * H t) →
    (∀ t, F t = (r t : ℂ) * Y t) →
    ∀ t,
      laguerreCurvature F t / (r t) ^ 2 =
        laguerreCurvature Y t -
          deriv (deriv (fun s => Real.log (r s))) t * ‖Y t‖ ^ 2

end MathlibPlus.Open.Analysis
