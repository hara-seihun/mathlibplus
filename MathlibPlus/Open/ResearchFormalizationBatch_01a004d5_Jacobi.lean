import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a004d5

open scoped BigOperators

/-- The admitted odd/even interlacing of the Cholesky coefficients. -/
def interlacedLiftCoefficients_claim8595
    (r s : ℕ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ k : ℕ, a (2 * k) = r k) ∧
    (∀ k : ℕ, 1 ≤ k → a (2 * k - 1) = s k)

private def sourceDecomposition (S U E : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, S k = (U k - U (k + 1)) / 2 + E k / 2

/-- The admitted weighted source summation-by-parts identity. -/
def weightedSourceSummationByParts_claim8599 : Prop :=
  ∀ (S U E Y : ℕ → ℝ), sourceDecomposition S U E →
    ∀ (A B : ℕ), A ≤ B →
      (∑ k ∈ Finset.Icc A B, S k * Y k) =
        (1 / 2 : ℝ) *
          (U A * Y A - U (B + 1) * Y B
            + ∑ k ∈ Finset.Icc (A + 1) B, U k * (Y k - Y (k - 1))
            + ∑ k ∈ Finset.Icc A B, E k * Y k)

/-- The admitted projective-imbalance identity in the Cholesky setting. -/
def projectiveImbalanceLift_claim8601 : Prop :=
  ∀ (q β r s : ℕ → ℝ),
    (∀ k : ℕ,
      q k = r k ^ 2 ∧ β (k + 1) = r k * s (k + 1) ∧
      r k ≠ 0 ∧ s (k + 1) ≠ 0) →
      ∀ k : ℕ,
        q k / β (k + 1) = r k / s (k + 1) ∧
        (q k / β (k + 1) - 1 = r k / s (k + 1) - 1)

/-- The admitted absolute source majorant. -/
def absoluteSourceMajorant_claim8611 : Prop :=
  ∀ (S U : ℕ → ℝ) (V : ℕ → ℕ → ℝ),
    (∀ A B : ℕ, A ≤ B →
      V A B = 2 * (∑ k ∈ Finset.Icc A B, S k) - U A + U (B + 1)) →
    ∀ A B : ℕ, A ≤ B →
      V A B ≤
        (2 * |∑ k ∈ Finset.Icc A B, S k| + |U A| + |U (B + 1)|)

/-- The admitted two exact adjacent logarithmic parity defects. -/
def adjacentParityDefects_claim8618 : Prop :=
  ∀ (n m : ℕ) (r s ell A B : ℕ → ℝ) (k : ℕ),
    1 ≤ m → m ≤ n - 1 → k = n - m →
    0 < r (k - 1) → 0 < r k → 0 < s k →
    (2 * Real.log (r (k - 1)) = ell m - ell (m + 1)) →
    (2 * Real.log (r k) = ell (m - 1) - ell m) →
    (2 * Real.log (s k) =
      (A (m - 1) - 2 * A m + A (m + 1)) + ell (m + 1) - ell m) →
    (2 * Real.log (s k) =
      (B (m - 1) - 2 * B m + B (m + 1)) + ell m - ell (m - 1)) →
      Real.log (r (k - 1) / s k) =
          ell m - ell (m + 1)
            - (1 / 2 : ℝ) * (A (m - 1) - 2 * A m + A (m + 1)) ∧
      Real.log (s k / r k) =
          (1 / 2 : ℝ) * (B (m - 1) - 2 * B m + B (m + 1))
            - (ell (m - 1) - ell m)

end MathlibPlus.Open.ResearchFormalizationBatch_01a004d5
