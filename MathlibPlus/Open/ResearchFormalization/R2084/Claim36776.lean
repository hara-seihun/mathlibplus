import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2084.Claim36776

noncomputable section

private def quadraticRecurrenceAt (T : ℕ → ℝ) (r p s : ℕ) : Prop :=
  T r ≤ max
    (3 * T (r - p))
    ((27 / 2 : ℝ) * ((s - 1 : ℕ) : ℝ) * (p : ℝ) * T (r - p) ^ 2)

private def correctedInductiveBound (B : ℝ) (a : ℕ)
    (T : ℕ → ℝ) (r : ℕ) : Prop :=
  T r ≤ B ^ r / ((r + 1 : ℕ) : ℝ) ^ a

private def halfRankPolynomialCorrection : Prop :=
  ∀ b a : ℕ, a > b + 1 →
    ∃ B₀ : ℝ, 1 < B₀ ∧
      ∀ B : ℝ, B₀ ≤ B →
        ∀ r p s : ℕ,
          0 < r → 2 * p ≥ r → p ≤ r → s ≤ r ^ b →
          (∀ T : ℕ → ℝ,
            (∀ u : ℕ, 0 ≤ T u) →
            correctedInductiveBound B a T (r - p) →
            quadraticRecurrenceAt T r p s →
            correctedInductiveBound B a T r ∧ T r ≤ B ^ r) ∧
          (((r - p : ℕ) : ℝ) ≥ (r : ℝ) / 4 →
            ((s - 1 : ℕ) : ℝ) * (p : ℝ) / (r : ℝ) ^ a ≤
              Real.rpow (r : ℝ)
                ((b + 1 : ℝ) - (a : ℝ))) ∧
          (((r - p : ℕ) : ℝ) < (r : ℝ) / 4 →
            Real.rpow B (((2 * (r - p) : ℕ) : ℝ) - (r : ℝ)) ≤
              Real.rpow B (-((r : ℝ) / 2)))

private def dyadicSupportCostAccumulation : Prop :=
  ∀ S : ℝ, 1 < S →
    ∀ L : ℕ → ℝ,
      (∀ k : ℕ,
        L (2 ^ (k + 1)) =
          ((2 ^ k : ℕ) : ℝ) * Real.log S + 2 * L (2 ^ k)) →
      (∀ k : ℕ,
        L (2 ^ k) / ((2 ^ k : ℕ) : ℝ) =
          L 1 + (k : ℝ) / 2 * Real.log S) ∧
      (∀ C : ℝ, ∃ k : ℕ,
        C < L (2 ^ k) / ((2 ^ k : ℕ) : ℝ))

/-- Iterated quadratic branches retain the doubled residual exponent, while
exact half-rank corrections and dyadic support costs remain explicit. -/
def unboundedStackingDoesNotAggregateRank_claim36776 : Prop :=
  (∀ (B : ℝ) (q : ℕ) (r : Fin (q + 1) → ℕ)
      (p : Fin q → ℕ),
    1 < B →
    (∀ j : Fin q, r j.succ + p j = r j.castSucc) →
    (∀ j : Fin q, 2 * p j ≤ r j.castSucc) →
    (2 ^ q : ℕ) * r (Fin.last q) ≥ r 0 ∧
    B ^ ((2 ^ q : ℕ) * r (Fin.last q)) ≥ B ^ (r 0) ∧
    ((∃ j : Fin q, 2 * p j < r j.castSucc) →
      (2 ^ q : ℕ) * r (Fin.last q) > r 0 ∧
      B ^ ((2 ^ q : ℕ) * r (Fin.last q)) > B ^ (r 0))) ∧
  halfRankPolynomialCorrection ∧
  dyadicSupportCostAccumulation

end

end MathlibPlus.Open.ResearchFormalization.R2084.Claim36776
