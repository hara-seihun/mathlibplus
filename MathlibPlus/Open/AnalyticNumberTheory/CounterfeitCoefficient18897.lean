import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.CounterfeitCoefficient18897

/-- Claim 18897: in the three-scale counterfeit theta family, the
integer-shell coefficient is the stated divisibility-indicator sequence.  The
second conjunct keeps that coefficient attached to the same integer-shell
series as the family. -/
noncomputable def counterfeitCoefficientFormula_claim18897 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → ∀ A B : ℕ,
    let theta : ℝ → ℝ := fun x =>
      ∑' k : ℤ, Real.exp (-Real.pi * (k : ℝ) ^ 2 * x)
    let Ψ : ℝ → ℝ := fun x =>
      (A : ℝ) * theta x +
        (B : ℝ) * theta ((p : ℝ) ^ 2 * x) +
          ((A * p : ℕ) : ℝ) * theta ((p : ℝ) ^ 4 * x)
    let a : ℕ → ℕ := fun n =>
      A + B * (if p ∣ n then 1 else 0) +
        (A * p) * (if p ^ 2 ∣ n then 1 else 0)
    (∀ n : ℕ,
      a n = A + B * (if p ∣ n then 1 else 0) +
        (A * p) * (if p ^ 2 ∣ n then 1 else 0)) ∧
      (∀ x : ℝ, 0 < x →
        Ψ x =
          ∑' n : ℤ, (a (Int.natAbs n) : ℝ) *
            Real.exp (-Real.pi * (n : ℝ) ^ 2 * x))

end MathlibPlus.Open.AnalyticNumberTheory.CounterfeitCoefficient18897
