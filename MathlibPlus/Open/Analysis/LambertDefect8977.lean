import MathlibPlus.Open.Analysis.ConsecutiveNormDenominator

open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 8977: the exact odd coefficient carrier has zero logarithmic
Lambert defect on every macroscopic filling block. -/
def claim8977 : Prop :=
  ∀ (p : ℕ → ℕ → Polynomial ℝ)
    (y : ∀ n k : ℕ, Fin k → ℝ)
    (r : ℕ → ℕ → ℝ),
    (∀ n k : ℕ,
      (p n k).Monic ∧
        (p n k).natDegree = k ∧
        p n k = ∏ j : Fin k,
          (Polynomial.X - Polynomial.C ((y n k j) ^ 2)) ∧
        (∀ j : Fin k, 0 < y n k j) ∧
        (∀ i j : Fin k, i.val < j.val → y n k j < y n k i)) →
    (∀ n k : ℕ, 0 < r n k) →
    (∀ n k : ℕ, 0 < k →
      r n (k - 1) ^ 2 =
        ((-1 : ℝ) ^ k * (p n k).eval 0) /
          ((-1 : ℝ) ^ (k - 1) * (p n (k - 1)).eval 0)) →
    (∀ α₀ α₁ : ℝ, 0 < α₀ → α₀ < α₁ →
      ∀ k₁ k₂ : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop,
          α₀ ≤ (k₁ n : ℝ) / (n : ℝ) ∧
            k₁ n ≤ k₂ n ∧
            (k₂ n : ℝ) / (n : ℝ) ≤ α₁) →
        Tendsto
          (fun n : ℕ =>
            (n : ℝ)⁻¹ *
              ∑ q ∈ Finset.Icc (k₁ n) (k₂ n),
                (Real.log (r n (q - 1)) -
                  Real.log (Real.log (n : ℝ) / (8 * (q : ℝ)))))
          atTop (𝓝 0)) →
    (∀ α₀ α₁ : ℝ, 0 < α₀ → α₀ < α₁ →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n q : ℕ,
          N ≤ n →
          1 ≤ q →
          α₀ ≤ (q : ℝ) / (n : ℝ) →
          (q : ℝ) / (n : ℝ) ≤ α₁ →
          |Real.log
            ((Real.log (n : ℝ) / (8 * (q : ℝ))) /
              compactLambertCoefficient (2 * q - 1))| < ε) →
    ∀ α₀ α₁ : ℝ, 0 < α₀ → α₀ < α₁ →
      ∀ k₁ k₂ : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop,
          α₀ ≤ (k₁ n : ℝ) / (n : ℝ) ∧
            k₁ n ≤ k₂ n ∧
            (k₂ n : ℝ) / (n : ℝ) ≤ α₁) →
        Tendsto
          (fun n : ℕ =>
            (n : ℝ)⁻¹ *
              ∑ q ∈ Finset.Icc (k₁ n) (k₂ n),
                Real.log
                  (r n (q - 1) /
                    compactLambertCoefficient (2 * q - 1)))
          atTop (𝓝 0)

end

end MathlibPlus.Open.Analysis
