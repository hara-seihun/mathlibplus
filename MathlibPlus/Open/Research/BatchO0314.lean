import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.BatchO0314

/-- The line quartic from the symmetric divisor-relocation pair. -/
def eLinePolynomial (b : ℝ) : Polynomial ℂ :=
  (Polynomial.X ^ 2 + Polynomial.C ((b : ℂ) ^ 2)) ^ 2

/-- The off-axis conjugate-pair quartic from the same pair. -/
def eOffPolynomial (a b : ℝ) : Polynomial ℂ :=
  (Polynomial.X ^ 2 -
      Polynomial.C (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2)) *
    (Polynomial.X ^ 2 -
      Polynomial.C (((a : ℂ) - (b : ℂ) * Complex.I) ^ 2))

/-- Upper-half-plane zero count by height, with multiplicity supplied by the
root multiset of the polynomial. -/
noncomputable def upperZeroCount (P : Polynomial ℂ) (T : ℝ) : ℕ := by
  classical
  exact (P.roots.filter (fun z => 0 < z.im ∧ z.im ≤ T)).card

/-- The two explicit quartics have the same upper zero-counting function. -/
def claim15334 : Prop :=
  ∀ (a b : ℝ), 0 < a → a < 1 / 2 → 0 < b →
    ∀ T : ℝ,
      upperZeroCount (eLinePolynomial b) T =
          upperZeroCount (eOffPolynomial a b) T ∧
        upperZeroCount (eLinePolynomial b) T =
          2 * (if b ≤ T then 1 else 0) ∧
        upperZeroCount (eOffPolynomial a b) T =
          2 * (if b ≤ T then 1 else 0)

end MathlibPlus.Open.Research.BatchO0314
