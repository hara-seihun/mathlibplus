import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim1698

noncomputable section

/-- The displayed principal product as a polynomial in the rational variable `b`. -/
def principalProductPolynomial (d : ℕ) : Polynomial ℚ :=
  (Nat.factorial d : Polynomial ℚ) *
    Finset.prod (Finset.range (d + 1)) (fun p =>
      Finset.prod (Finset.range (d + 1)) (fun q =>
        if p < q then
          2 * Polynomial.X + Polynomial.C (p + q + 1 : ℚ)
        else 1))

/-- Evaluation of the displayed principal product at the real half-shift `b`. -/
def principalProductValue (b : ℝ) (d : ℕ) : ℝ :=
  Polynomial.eval₂ (algebraMap ℚ ℝ) b (principalProductPolynomial d)

/-- Claim 1698: the half-shift, the value of `Y`, and the exact principal
product over all pairs `0 ≤ p < q ≤ d`. -/
def claim1698_halfShiftAndPrincipalProduct : Prop :=
  ∀ (a b : ℝ) (d : ℕ),
    b = a - 1 / 2 →
      let Y : ℝ := 2 * a + d
      let P_d : ℝ := principalProductValue b d
      Y = 2 * b + d + 1 ∧
        P_d =
          (Nat.factorial d : ℝ) *
            Finset.prod (Finset.range (d + 1)) (fun p =>
              Finset.prod (Finset.range (d + 1)) (fun q =>
                if p < q then 2 * b + (p + q + 1 : ℕ) else 1))

end

end MathlibPlus.Open.ResearchFormalization.Claim1698
