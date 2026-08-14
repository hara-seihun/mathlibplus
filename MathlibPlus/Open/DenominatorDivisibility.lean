import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open

namespace DenominatorDivisibility

open Polynomial

/-- The linear factor indexed by a pair in the principal product. -/
def pairFactor (p q : ℕ) : Polynomial ℝ :=
  2 * X + C ((p + q + 1 : ℕ) : ℝ)

/-- The principal pair product `∏_{0 ≤ p < q ≤ d} (2 b + p + q + 1)`,
with `b` represented by the polynomial variable. -/
def principalPairProduct (d : ℕ) : Polynomial ℝ :=
  ∏ p ∈ Finset.range (d + 1),
    ∏ q ∈ Finset.range (d + 1),
      if p < q then pairFactor p q else 1

/-- The polynomial `Y = 2 b + d + 1`. -/
def y (d : ℕ) : Polynomial ℝ :=
  2 * X + C ((d + 1 : ℕ) : ℝ)

/-- Rising factorials of polynomials. -/
def risingFactorial (z : Polynomial ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ c ∈ Finset.range n, (z + C (c : ℝ))

/-- The row-denominator factor indexed by `c`. -/
def rowFactor (d c : ℕ) : Polynomial ℝ :=
  2 * X + C ((d + c + 1 : ℕ) : ℝ)

/-- The column-denominator factor indexed by `c`. -/
def columnFactor (d c : ℕ) : Polynomial ℝ :=
  2 * X + C ((d + 1 - c : ℕ) : ℝ)

/-- The row denominator `(Y)_n`. -/
def rowDenominator (d n : ℕ) : Polynomial ℝ :=
  risingFactorial (y d) n

/-- The column denominator `(Y-n+1)_n`. -/
def columnDenominator (d n : ℕ) : Polynomial ℝ :=
  risingFactorial (y d - C (n : ℝ) + C 1) n

/-- The product left after removing the row factors at `(c,d)`, `c<n`. -/
def rowRemainingProduct (d n : ℕ) : Polynomial ℝ :=
  ∏ p ∈ Finset.range (d + 1),
    ∏ q ∈ Finset.range (d + 1),
      if p < q ∧ ¬ (q = d ∧ p < n) then pairFactor p q else 1

/-- The product left after removing the column factors at `(0,d-c)`, `c<n`. -/
def columnRemainingProduct (d n : ℕ) : Polynomial ℝ :=
  ∏ p ∈ Finset.range (d + 1),
    ∏ q ∈ Finset.range (d + 1),
      if p < q ∧ ¬ (p = 0 ∧ ∃ c, c < n ∧ q = d - c) then pairFactor p q else 1

/-- Every nonzero coefficient through the degree is strictly positive. -/
def strictlyPositiveCoefficients (f : Polynomial ℝ) : Prop :=
  ∀ k ≤ f.natDegree, 0 < f.coeff k

/-- For `n ≤ d`, the row and column denominator factors occur at the
specified distinct pairs of the principal pair product; both denominators
therefore divide that product, and each corresponding remaining product has
strictly positive coefficients. -/
def denominatorDivisibilityWitnesses : Prop :=
  ∀ n d : ℕ, n ≤ d →
    (∀ c < n,
      c < d ∧
      rowFactor d c = pairFactor c d ∧
      rowFactor d c ∣ principalPairProduct d) ∧
    (∀ c < n,
      0 < d - c ∧
      columnFactor d c = pairFactor 0 (d - c) ∧
      columnFactor d c ∣ principalPairProduct d) ∧
    (∀ ⦃c₁ c₂ : ℕ⦄, c₁ < n → c₂ < n → c₁ ≠ c₂ →
      (c₁, d) ≠ (c₂, d)) ∧
    (∀ ⦃c₁ c₂ : ℕ⦄, c₁ < n → c₂ < n → c₁ ≠ c₂ →
      (0, d - c₁) ≠ (0, d - c₂)) ∧
    rowDenominator d n ∣ principalPairProduct d ∧
    columnDenominator d n ∣ principalPairProduct d ∧
    principalPairProduct d =
      rowDenominator d n * rowRemainingProduct d n ∧
    principalPairProduct d =
      columnDenominator d n * columnRemainingProduct d n ∧
    strictlyPositiveCoefficients (rowRemainingProduct d n) ∧
    strictlyPositiveCoefficients (columnRemainingProduct d n)

end DenominatorDivisibility

end MathlibPlus.Open
