import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The carrier, logarithmic derivative, phase, and decorated residual operators
    appearing in the signed-linear carrier calculation. -/
def carrierDecoratedResidualDefinitions
    (A T : ℝ → ℂ)
    (a b omega : ℝ → ℂ)
    (p c : ℝ → ℝ)
    (P0T P1T : ℝ → ℂ)
    (_hA : ContDiff ℝ 2 A)
    (_hA0 : ∀ x, A x ≠ 0) : Prop :=
  (∀ x, a x = deriv A x / A x) ∧
  (∀ x, b x = deriv a x) ∧
  (∀ x, omega x = A x / (‖A x‖ : ℂ)) ∧
  (∀ x, p x = Complex.im (a x)) ∧
  (∀ x, c x = 2 * (p x) ^ 2 - Complex.re (b x)) ∧
  (∀ x,
    P0T x =
      -deriv (fun y : ℝ => deriv T y) x
        - 4 * Complex.I * (p x : ℂ) * deriv T x
        + 2 * (c x : ℂ) * T x) ∧
  (∀ x,
    P1T x =
      -deriv (fun y : ℝ => deriv T y) x - 2 * b x * T x)

/-- Supremum norm on a real closed interval, written without introducing a
    separate normed-function space. -/
noncomputable def intervalSupNorm (a b : ℝ) (f : ℝ → ℂ) : ℝ :=
  sSup ((fun x => ‖f x‖) '' Set.Icc a b)

/-- The one-dimensional Sobolev--Filon estimate for the two decorated
    residuals.  The pointwise inequalities are the interval supremum-norm
    conclusion. -/
def sobolevFilonSupremumEstimate
    (a b L : ℝ)
    (P0T P1T : ℝ → ℂ)
    (V0 V1 W0 W1 nu0 nu1 : ℝ) : Prop :=
  (0 < L ∧ b - a = L ∧
      (∫ x in a..b, ‖P0T x‖ ^ 2) ≤ V0 ∧
      (∫ x in a..b,
          ‖deriv P0T x - Complex.I * (nu0 : ℂ) * P0T x‖ ^ 2) ≤ W0 ∧
      (∫ x in a..b, ‖P1T x‖ ^ 2) ≤ V1 ∧
      (∫ x in a..b,
          ‖deriv P1T x - Complex.I * (nu1 : ℂ) * P1T x‖ ^ 2) ≤ W1) →
    (intervalSupNorm a b P0T ≤ Real.sqrt (V0 / L + 2 * Real.sqrt (V0 * W0)) ∧
      intervalSupNorm a b P1T ≤ Real.sqrt (V1 / L + 2 * Real.sqrt (V1 * W1)))

/-- The selected-branch coordinate definitions, with the branch function
    supplied by the surrounding analytic construction. -/
def selectedBranchCoordinateFunctions
    (t : ℝ)
    (alpha : ℂ → ℂ)
    (s sStar : ℂ → ℂ)
    (b : ℕ → ℝ) : Prop :=
  (∀ z, s z = (1 - Complex.I * z) / 2) ∧
  (∀ z, sStar z = s z + (t : ℂ) / 2 * alpha (s z)) ∧
  (∀ n, b n = Real.exp (t * (Real.log (n : ℝ)) ^ 2 / 4))

end MathlibPlus.Open.ResearchFormalization
