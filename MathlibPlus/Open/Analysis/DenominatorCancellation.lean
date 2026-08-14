import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

noncomputable section

/-- The polynomial variable is the half-shift variable `b`. -/
def bVariable : Polynomial ℝ := Polynomial.X

/-- The factor indexed by a pair `(p,q)` in the principal product. -/
def pairPolynomial (pair : ℤ × ℤ) : Polynomial ℝ :=
  2 * bVariable + Polynomial.C (((pair.1 + pair.2 + 1 : ℤ) : ℝ))

/-- The pairs `0 ≤ p < q ≤ d` occurring in the principal product. -/
def principalPairs (d : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (d + 1)).biUnion (fun p =>
    (Finset.Icc (p + 1) d).image (fun q : ℕ => ((p : ℤ), (q : ℤ))))

/-- `P_d(b) = d! ∏_{0 ≤ p < q ≤ d} (2b+p+q+1)`. -/
def principalProduct (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (d.factorial : ℝ) *
    Finset.prod (principalPairs d) (fun pair => pairPolynomial pair)

/-- `Y = 2b+d+1`. -/
def principalY (d : ℕ) : Polynomial ℝ :=
  2 * bVariable + Polynomial.C (((d + 1 : ℕ) : ℝ))

/-- The rising product `(Y)_m = ∏_{i=0}^{m-1}(Y+i)`. -/
def risingProduct (y : Polynomial ℝ) (m : ℕ) : Polynomial ℝ :=
  Finset.prod (Finset.range m) (fun i => y + Polynomial.C (i : ℝ))

/-- `Δ_(n,k) = (Y-1)(Y)_(k-1)(Y)_n`. -/
def denominator (d n k : ℕ) : Polynomial ℝ :=
  (principalY d - 1) * risingProduct (principalY d) (k - 1) *
    risingProduct (principalY d) n

/-- The pair occurrences listed in the denominator-cancellation claim. -/
def cancellationPairs (d n k : ℕ) : List (ℤ × ℤ) :=
  [(0, (d : ℤ) - 1)] ++
    (List.range (k - 1)).flatMap (fun i =>
      [((i : ℤ), (d : ℤ)), (((i : ℤ) + 1), (d : ℤ) - 1)]) ++
    (List.range (n + 1 - k)).map (fun i =>
      (((k + i : ℕ) : ℤ) - 1, (d : ℤ)))

/-- The product of the factors indexed by the listed pair occurrences. -/
def cancellationProduct (d n k : ℕ) : Polynomial ℝ :=
  ((cancellationPairs d n k).map pairPolynomial).prod

/-- The principal factors not used by the listed cancellation pairs. -/
def remainingPairs (d n k : ℕ) : Finset (ℤ × ℤ) :=
  (principalPairs d).filter
    (fun pair => pair ∉ (cancellationPairs d n k).toFinset)

/-- The product left after cancellation, including the positive scalar `d!`. -/
def remainingProduct (d n k : ℕ) : Polynomial ℝ :=
  Polynomial.C (d.factorial : ℝ) *
    Finset.prod (remainingPairs d n k) (fun pair => pairPolynomial pair)

/-- A positive affine (hence linear-in-`b`) polynomial. -/
def PositiveLinearInB (f : Polynomial ℝ) : Prop :=
  ∃ slope intercept : ℝ,
    0 ≤ slope ∧ 0 < intercept ∧
      f = Polynomial.C slope * bVariable + Polynomial.C intercept

/-- Positivity of every factor in the concrete remaining principal product. -/
def RemainingFactorsPositive (d n k : ℕ) : Prop :=
  PositiveLinearInB (Polynomial.C (d.factorial : ℝ)) ∧
    ∀ pair ∈ remainingPairs d n k, PositiveLinearInB (pairPolynomial pair)

/--
Denominator cancellation in the principal product: under the stated bound on `d`,
the denominator factors occur distinctly through the listed pairs, divide the
principal product, and leave a product of positive linear polynomials in `b`.
-/
def denominatorCancellationPrincipalProduct : Prop :=
  ∀ d n k : ℕ, d ≥ max n (k + 1) →
    List.Nodup (cancellationPairs d n k) ∧
      (∀ pair ∈ cancellationPairs d n k, pair ∈ principalPairs d) ∧
      denominator d n k = cancellationProduct d n k ∧
      denominator d n k ∣ principalProduct d ∧
      principalProduct d / denominator d n k = remainingProduct d n k ∧
      RemainingFactorsPositive d n k

end
end MathlibPlus.Open
