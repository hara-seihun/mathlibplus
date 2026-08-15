import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

/-- Claim 3450 together with the exact independent expansion supplied as repair context. -/
def baezDuarteCoefficientFormula : Prop :=
  ∀ k : ℕ,
    (∑' n : {n : ℕ // 1 ≤ n},
      ((ArithmeticFunction.moebius (n : ℕ) : ℤ) : ℂ) /
          ((n : ℂ) ^ 2) * (1 - 1 / ((n : ℂ) ^ 2)) ^ k) =
      ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℂ) ^ j) * (k.choose j : ℂ) /
          riemannZeta ((2 * j + 2 : ℕ) : ℂ)

end MathlibPlus.Open.AdmittedBatch
