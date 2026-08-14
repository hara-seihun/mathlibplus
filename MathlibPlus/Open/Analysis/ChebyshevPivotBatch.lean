import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ChebyshevPivotBatch

noncomputable section

private def nodalPolynomial (x : ℕ → ℝ) (j : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (x i))

private def insertionValue (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  |(nodalPolynomial x j).eval (x j)|

private def lebesguePivot (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j,
    |∏ k ∈ Finset.range j,
      if k = i then 1 else (x j - x k) / (x i - x k)|

private def nodesInInterval (x : ℕ → ℝ) (n : ℕ) (D : ℝ) : Prop :=
  ∃ a : ℝ, ∀ i : ℕ, i < n → x i ∈ Set.Icc a (a + D)

private def pivotIdentity (x : ℕ → ℝ) (S : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ j : ℕ, 2 ≤ j → j ≤ n →
    1 + lebesguePivot x (j - 1) = S j * insertionValue x (j - 1)

/-- Claim 46129: the logarithmic pivot lower bound under the exact pivot
identity, an interval of length `D`, and the upper bound on `S_n`. -/
def claim46129 : Prop :=
  ∀ (n : ℕ) (D C : ℝ) (x S : ℕ → ℝ),
    2 ≤ n → 0 < D → 0 < C →
      nodesInInterval x n D →
      pivotIdentity x S n →
      S n ≤ C * (4 / D) ^ (n - 1) →
      2 * ∑ j ∈ Finset.Icc 2 n,
          Real.log (1 + lebesguePivot x (j - 1)) ≥
        (n : ℝ) * Real.log n -
          2 * ((n - 1 : ℕ) : ℝ) * Real.log 2 -
          (n : ℝ) * Real.log C

/-- Claim 46132: the geometric-mean form of the same pivot bound. -/
def claim46132 : Prop :=
  ∀ (n : ℕ) (D C : ℝ) (x S : ℕ → ℝ),
    2 ≤ n → 0 < D → 0 < C →
      nodesInInterval x n D →
      pivotIdentity x S n →
      S n ≤ C * (4 / D) ^ (n - 1) →
      Real.rpow
          (∏ j ∈ Finset.Icc 2 n, (1 + lebesguePivot x (j - 1)))
          ((1 : ℝ) / (n - 1 : ℝ)) ≥
        (1 / 2 : ℝ) *
          Real.rpow ((n : ℝ) / C)
            ((n : ℝ) / (2 * (n - 1 : ℕ) : ℝ))

end
end MathlibPlus.Open.Analysis.ChebyshevPivotBatch
