import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.CenterFlatPolynomialLowerBound

noncomputable section

/-- The real-even entire order-at-most-one hypotheses in Record 18. -/
def realEvenEntireOrderAtMostOne (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧
    (∀ z : ℂ, G (-z) = G z) ∧
    (∀ x : ℝ, (G (x : ℂ)).im = 0) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, 0 < A ∧
        ∀ z : ℂ,
          ‖G z‖ ≤ A * Real.exp (Real.rpow ‖z‖ (1 + ε)))

/-- Claim 15477: the paired real-zero product has the stated imaginary-axis
lower bound, and a nonzero complex polynomial has an eventual polynomial
lower bound on that axis. -/
def claim15477 : Prop :=
  (∀ (G : ℂ → ℂ),
    realEvenEntireOrderAtMostOne G →
    (∀ z : ℂ, G z = 0 → z.im = 0) →
    G ≠ 0 →
    ∃ (ι : Type*) (hι : Countable ι) (C : ℂ) (m : ℕ) (x : ι → ℝ),
      letI := hι
      C ≠ 0 ∧
        (∀ k : ι, x k ≠ 0) ∧
        Summable (fun k : ι => (x k)⁻¹ ^ 2) ∧
        (∀ y : ℝ, 0 < y →
          ‖G (-Complex.I * (y : ℂ))‖ =
            ‖C‖ * y ^ (2 * m) *
              ∏' k : ι, (1 + y ^ 2 / (x k) ^ 2)) ∧
        (∀ y : ℝ, 0 < y →
          ‖G (-Complex.I * (y : ℂ))‖ ≥ ‖C‖ * y ^ (2 * m))) ∧
  (∀ P : Polynomial ℂ, P ≠ 0 →
    ∃ c Y : ℝ, 0 < c ∧
      ∀ y : ℝ, Y ≤ y →
        ‖P.eval (-Complex.I * (y : ℂ))‖ ≥ c * y ^ P.natDegree)

end

end MathlibPlus.Open.AnalyticNumberTheory.CenterFlatPolynomialLowerBound
