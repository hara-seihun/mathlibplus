import MathlibPlus.Open.Analysis.CompletedThetaToeplitz

namespace MathlibPlus.Open.Analysis.CompletedThetaPositiveDefinite11936

noncomputable section

open MeasureTheory

/-- The completed-theta Fourier transform on the real axis. -/
def completedThetaFourier (x : ℝ) : ℂ :=
  ∫ u : ℝ,
    (completedThetaSource u : ℂ) *
      Complex.exp (Complex.I * (x : ℂ) * (u : ℂ))

/-- The Fourier transform of the two-copy autocorrelation. -/
def completedThetaAutocorrelationFourier (x : ℝ) : ℂ :=
  ∫ y : ℝ,
    (completedThetaAutocorrelation y : ℂ) *
      Complex.exp (2 * Complex.I * (x : ℂ) * (y : ℂ))

/-- The finite quadratic-form criterion for positive definiteness of `A`. -/
def completedThetaPositiveDefinite : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      c i * completedThetaAutocorrelation (x i - x j) * c j

/-- The Fourier-square nonnegativity and the positive-definiteness conclusion
for the exact completed-theta autocorrelation carrier. -/
def completedThetaAutocorrelationPositiveDefinite : Prop :=
  (∀ x : ℝ,
    (completedThetaFourier x).im = 0 ∧
      completedThetaAutocorrelationFourier x =
        (1 / 2 : ℂ) * (completedThetaFourier x) ^ 2 ∧
      (completedThetaAutocorrelationFourier x).im = 0 ∧
      0 ≤ (completedThetaAutocorrelationFourier x).re) ∧
    completedThetaPositiveDefinite

end

end MathlibPlus.Open.Analysis.CompletedThetaPositiveDefinite11936
