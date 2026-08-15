import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

/-- A coefficient sequence on `ℤ`, with the required zero extension and positivity. -/
def PositiveZeroExtendedSequence (f : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, n < 0 → f n = 0) ∧
    (∀ n : ℤ, 0 ≤ n → 0 < f n)

/-- Every Toeplitz minor of order at most `r` is nonnegative. -/
def IsPFSequence (f : ℤ → ℝ) (r : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ r →
    ∀ (rows cols : Fin q → ℤ),
      StrictMono rows → StrictMono cols →
        0 ≤ Matrix.det (fun i j => f (cols j - rows i))

/-- The power series with coefficients `f` converges at every complex argument. -/
def IsEntirePowerSeries (f : ℤ → ℝ) : Prop :=
  ∀ z : ℂ, Summable (fun n : ℕ => (f (n : ℤ) : ℂ) * z ^ n)

/-- The coefficient sequence is not eventually zero. -/
def IsNonPolynomial (f : ℤ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f (n : ℤ) ≠ 0

/-- Coefficients of the exterior Laurent expansion of `F z / (z - α)`. -/
def exteriorLaurentCoefficient (f : ℤ → ℝ) (α : ℝ) (n : ℤ) : ℝ :=
  ∑' ell : ℕ, α ^ ell * f (n + (ell : ℤ) + 1)

/-- The endpoint Laurent block `B_{r,k}`. -/
def endpointLaurentBlock (f : ℤ → ℝ) (α : ℝ) (r k : ℕ) :
    Matrix (Fin (r + 1)) (Fin r) ℝ :=
  fun i j =>
    exteriorLaurentCoefficient f α
      ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ))

/-- The square block obtained by deleting row `m` from `B_{r,k}`. -/
def deletedEndpointBlock (f : ℤ → ℝ) (α : ℝ) (r k : ℕ)
    (m : Fin (r + 1)) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => endpointLaurentBlock f α r k (Fin.succAbove m i) j

/-- The endpoint cofactor `Δ_m(r,k)`. -/
def endpointCofactor (f : ℤ → ℝ) (α : ℝ) (r k : ℕ)
    (m : Fin (r + 1)) : ℝ :=
  Matrix.det (deletedEndpointBlock f α r k m)

/-- An entry of a restricted source column. -/
def sourceEntry (f : ℤ → ℝ) (s i : ℕ) : ℝ :=
  f ((s : ℤ) - (i : ℤ))

/-- The adjacent-row, first-two-column source minor. -/
def adjacentSourceMinor (f : ℤ → ℝ) (k i : ℕ) : ℝ :=
  sourceEntry f (k + 1) i * sourceEntry f (k + 2) (i + 1) -
    sourceEntry f (k + 2) i * sourceEntry f (k + 1) (i + 1)

/-- The two alternatives for the positive adjacent minor at rank three. -/
def StrictOrHardEdgeAdjacentMinor (f : ℤ → ℝ) (k i : ℕ) : Prop :=
  let n : ℤ := (k + 1 : ℤ) - (i : ℤ)
  (1 ≤ n ∧ f n ^ 2 > f (n - 1) * f (n + 1)) ∨
    (n = 0 ∧ adjacentSourceMinor f k i = f 0 ^ 2 ∧ 0 < f 0 ^ 2)

/-- The initial source column is nonzero after any rank-two row deletion. -/
def RankTwoInitialColumnNonzero (f : ℤ → ℝ) (k : ℕ)
    (m : Fin 3) : Prop :=
  ∃ i : Fin 3, i ≠ m ∧ sourceEntry f (k + 1) i.val ≠ 0

/-- Every rank-three deleted-row set contains the required adjacent pair. -/
def RankThreeDeletedRowsHaveAdjacentMinor (f : ℤ → ℝ) (k : ℕ)
    (m : Fin 4) : Prop :=
  ∃ i : ℕ, i < 3 ∧ i ≠ m.val ∧ i + 1 ≠ m.val ∧
    0 < adjacentSourceMinor f k i ∧ StrictOrHardEdgeAdjacentMinor f k i

/--
Rank-two and rank-three endpoint cofactors are strict for positive,
nonpolynomial entire `PF₃` sequences, with the rank-two nonzero initial
column and the rank-three adjacent-minor alternatives included explicitly.
-/
def rankTwoAndRankThreeEndpointCofactorsStrict : Prop :=
  ∀ (f : ℤ → ℝ),
    PositiveZeroExtendedSequence f →
    IsNonPolynomial f →
    IsEntirePowerSeries f →
    IsPFSequence f 3 →
    ∀ α : ℝ, 0 < α →
      (∀ k : ℕ, 1 ≤ k →
        ∀ m : Fin 3,
          0 < endpointCofactor f α 2 k m ∧
            RankTwoInitialColumnNonzero f k m) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∀ m : Fin 4,
          0 < endpointCofactor f α 3 k m ∧
            RankThreeDeletedRowsHaveAdjacentMinor f k m)

end

end MathlibPlus.Open.Research
