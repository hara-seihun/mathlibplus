import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Algebra.ProductTransferBatch

/-- The finite product carrier used by the coefficient-transfer statement. -/
def productPolynomial {n : ℕ} (F : Fin n → Polynomial ℝ) : Polynomial ℝ :=
  ∏ i : Fin n, F i

/-- Claim 37136: after equal constant terms and the displayed first-delay
coefficient data, all coefficients below the minimum delay vanish and the
coefficient at the minimum delay is the stated sum over active occurrences. -/
def claim37136 : Prop :=
  ∀ (n : ℕ) (F G : Fin n → Polynomial ℝ) (U : Fin n → ℝ)
      (qι : Fin n → ℕ) (δ : Fin n → ℝ) (q : ℕ),
    0 < n →
    (∀ i : Fin n, (F i).coeff 0 = U i ∧ (G i).coeff 0 = U i) →
    ((∃ i : Fin n, qι i = q) ∧ (∀ i : Fin n, q ≤ qι i)) →
    (∀ i : Fin n, ∀ t < qι i, (F i - G i).coeff t = 0) →
    (∀ i : Fin n, (F i - G i).coeff (qι i) = δ i) →
      (∀ t < q,
        (productPolynomial F - productPolynomial G).coeff t = 0) ∧
      (productPolynomial F - productPolynomial G).coeff q =
        ∑ i : Fin n,
          if qι i = q then
            δ i * ∏ j : Fin n, if j = i then 1 else U j
          else 0

end MathlibPlus.Open.Algebra.ProductTransferBatch
