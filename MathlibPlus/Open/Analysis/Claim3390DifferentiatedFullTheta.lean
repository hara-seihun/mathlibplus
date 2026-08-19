import MathlibPlus.Open.Analysis.Claim3381

open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim3390

open MathlibPlus.Open.Analysis.Claim3381

noncomputable def realOrderThetaMoment (x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (u / 2) * primitiveCompletedTheta u * Real.rpow u (2 * x)

noncomputable def realOrderLogMoment (x : ℝ) : ℝ :=
  Real.log
    ((2 : ℝ) / Real.Gamma (2 * x + 1) * realOrderThetaMoment x)

noncomputable def realOrderLambertScale (x : ℝ) : ℝ :=
  lambertW₀ (2 * x / Real.pi)

noncomputable def realOrderGamma (x : ℝ) : ℝ :=
  realOrderLambertScale x / (1 + realOrderLambertScale x)

noncomputable def realOrderCentralSecondDifference
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + 1) - 2 * f x + f (x - 1)

noncomputable def realOrderCurvature (x : ℝ) : ℝ :=
  -realOrderCentralSecondDifference realOrderLogMoment x

noncomputable def fullThetaCurvatureError (x : ℝ) : ℝ :=
  deriv (fun y : ℝ =>
    deriv (fun z : ℝ => realOrderLogMoment z) y) x +
    2 * realOrderGamma x / x

/-- The full-theta real-order curvature estimate and its finite-difference
consequences, with the fixed primitive theta series as its carrier. -/
def differentiatedFullThetaSaddleSymbol : Prop :=
  (∀ j : ℕ, ∃ C X : ℝ,
    0 ≤ C ∧ 0 < X ∧
      ∀ x : ℝ, X ≤ x →
        |iteratedDeriv j fullThetaCurvatureError x| ≤
          C *
            (1 / (x ^ (j + 1) * realOrderLambertScale x ^ 2) +
              1 / x ^ (j + 2))) ∧
  (∃ C X : ℝ,
    0 ≤ C ∧ 0 < X ∧
      ∀ x : ℝ, X ≤ x →
        |realOrderCurvature x - 2 * realOrderGamma x / x| ≤
          C *
            (1 / (x * realOrderLambertScale x ^ 2) +
              1 / x ^ 2)) ∧
  (∀ j : ℕ, ∃ C X : ℝ,
    0 ≤ C ∧ 0 < X ∧
      ∀ x : ℝ, X ≤ x →
        |iteratedDeriv j realOrderCurvature x| ≤
          C * (1 / x ^ (j + 1)))

end MathlibPlus.Open.Analysis.Claim3390
