import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ChebyshevPivotClaim46115

noncomputable section

/-- The nodal polynomial through the first `j` entries of a real sequence. -/
def nodalPolynomial (x : ℕ → ℝ) (j : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (x i))

/-- The absolute insertion value at the next node. -/
def insertionValue (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  |(nodalPolynomial x j).eval (x j)|

/-- The pre-insertion Lebesgue pivot at the next node. -/
def lebesguePivot (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j,
    |∏ k ∈ Finset.range j,
      if k = i then 1 else (x j - x k) / (x i - x k)|

/-- The reciprocal-derivative normalization of the first `j` nodes. -/
def reciprocalDerivativeNormalization (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j,
    1 / |((nodalPolynomial x j).derivative.eval (x k))|

/-- The absolute Vandermonde product of the first `n` nodes. -/
def vandermonde (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    ∏ k ∈ Finset.range i, |x i - x k|

/-- The exact pre-insertion identity and insertion-value Vandermonde factorization
for every finite prefix of a distinct nested real interpolation sequence. -/
def claim46115 : Prop :=
  ∀ (n : ℕ) (x : ℕ → ℝ),
    1 ≤ n →
    Function.Injective x →
    (∀ j : ℕ, 1 ≤ j → j < n →
      1 + lebesguePivot x j =
        reciprocalDerivativeNormalization x (j + 1) * insertionValue x j) ∧
    vandermonde x n =
      ∏ j ∈ Finset.range n, insertionValue x j

end
end MathlibPlus.Open.Analysis.ChebyshevPivotClaim46115
