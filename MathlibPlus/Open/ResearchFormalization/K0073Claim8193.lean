import MathlibPlus.Open.ExactEnclosingDeterminantSign

namespace MathlibPlus.Open.ResearchFormalization.K0073Claim8193

noncomputable section

open MathlibPlus.Open

/-- The prefix of an order-`k+1` row or column list. -/
def prefixList {k : ℕ} (v : Fin (k + 1) → ℤ) : Fin k → ℤ :=
  fun i => v i.castSucc

/-- The nested order-`k` Toeplitz minor. -/
def nestedToeplitzMinor {k : ℕ} (f : ℤ → ℝ)
    (rows cols : Fin (k + 1) → ℤ) : ℝ :=
  toeplitzMinor f (prefixList rows) (prefixList cols)

/-- The order-`k+1` minor after replacing its last row by `s`. -/
def replacedLastRowMinor {k : ℕ} (f : ℤ → ℝ)
    (rows cols : Fin (k + 1) → ℤ) (s : ℤ) : ℝ :=
  toeplitzMinor f (snoc (prefixList rows) s) cols

/-- The last-column relation on all selected rows. -/
def lastColumnRelation {k : ℕ} (f : ℤ → ℝ)
    (rows cols : Fin (k + 1) → ℤ) (coefficients : Fin k → ℝ) : Prop :=
  ∀ i : Fin (k + 1),
    oneSidedToeplitz f (rows i) (cols (Fin.last k)) =
      ∑ j : Fin k,
        coefficients j * oneSidedToeplitz f (rows i) (cols j.castSucc)

/-- Claim 8193: a vanishing nonforced minor with positive nested minor has a
unique eliminated last column; its residuals have the exact determinant and
nonnegativity conclusions on every later row. -/
def claim8193 : Prop :=
  ∀ (k : ℕ) (f : ℤ → ℝ)
    (rows cols : Fin (k + 1) → ℤ),
    (∀ n : ℤ, n < 0 → f n = 0) →
    StrictMono rows → StrictMono cols →
    (∀ j : Fin (k + 1), rows j ≤ cols j) →
    toeplitzMinor f rows cols = 0 →
    0 < nestedToeplitzMinor f rows cols →
    toeplitzTotallyNonnegativeThrough f (k + 1) →
    ∃ coefficients : Fin k → ℝ,
      lastColumnRelation f rows cols coefficients ∧
      (∀ other : Fin k → ℝ,
        lastColumnRelation f rows cols other → other = coefficients) ∧
      (∀ s : ℤ, rows (Fin.last k) < s →
        replacedLastRowMinor f rows cols s =
          nestedToeplitzMinor f rows cols *
            toeplitzResidual f cols coefficients s ∧
        0 ≤ toeplitzResidual f cols coefficients s)

end

end MathlibPlus.Open.ResearchFormalization.K0073Claim8193
