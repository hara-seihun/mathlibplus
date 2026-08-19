import MathlibPlus.Open.Formalization.K0127

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Formalization.K0127.Claim8931

noncomputable section

/-- The polynomial carrier `p_n(x)=∏_{j=1}^n(x-y_{n,j}²)` on the exact
finite index interval. -/
def liftedGaussianZeroPolynomial
    (y : ℕ → ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.Icc 1 n,
    (Polynomial.X - Polynomial.C ((y n j) ^ 2))

/-- The normalized empirical Gaussian-node measure
`ν_n=n⁻¹∑_{j=1}^n δ_{y_{n,j}}`. -/
noncomputable def liftedGaussianNodeMeasure
    (y : ℕ → ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  MathlibPlus.Open.Formalization.K0127.gaussianNodeMeasure y n

/-- The exact positive, strictly ordered Gaussian-zero setup accompanying the
polynomial and its lifted empirical measure. -/
def liftedGaussianZeroSetup
    (p : ℕ → Polynomial ℝ) (y : ℕ → ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ x : ℝ,
      Polynomial.eval x (p n) =
        Polynomial.eval x (liftedGaussianZeroPolynomial y n)) ∧
      (∀ j ∈ Finset.Icc 1 n, 0 < y n j) ∧
      (∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
        j < k → y n k < y n j)

end

end MathlibPlus.Open.Formalization.K0127.Claim8931
