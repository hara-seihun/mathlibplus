import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def iteratedDerivative : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | n + 1, p => iteratedDerivative n p.derivative

/-- The all-rank Karlin determinant with the stated sign normalization. -/
noncomputable def karlinDeterminant (m : ℕ) (f : Polynomial ℝ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      (iteratedDerivative ((i : ℕ) + (j : ℕ)) f).eval x)

/-- Every zero of the real polynomial is real and nonpositive. -/
def allZerosRealNonpositive (f : Polynomial ℝ) : Prop :=
  ∀ z : ℂ,
    Polynomial.eval₂ (algebraMap ℝ ℂ) z f = 0 →
      z.im = 0 ∧ z.re ≤ 0

/-- All-rank positivity through degree six. -/
def allRankPositivityThroughDegreeSix : Prop :=
  ∀ f : Polynomial ℝ,
    0 < f.leadingCoeff →
    f.natDegree ≤ 6 →
    allZerosRealNonpositive f →
    ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, 0 ≤ x →
      karlinDeterminant m f x ≥ 0

end MathlibPlus.Open.Analysis
