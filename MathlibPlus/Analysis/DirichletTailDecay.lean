import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 3620: increasing the real exponent on an integer base at least two
has the exact pointwise tail comparison. -/
def realPowerTailComparison_claim3620 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ₁ σ : ℝ, σ₁ ≤ σ →
    (n : ℝ) ^ (-σ) ≤
      (2 : ℝ) ^ (-(σ - σ₁)) * (n : ℝ) ^ (-σ₁)

/-- Claim 3621: absolute summability on the integer tail transfers to every
larger real abscissa with the exact factor `2 ^ (-(σ - σ₁))`. -/
def summabilityShiftDecay : Prop :=
  ∀ (b : ℕ → ℂ) (σ₁ σ : ℝ), σ₁ ≤ σ →
    Summable
      (fun n : {n : ℕ // 2 ≤ n} =>
        ‖b n.1‖ * (n.1 : ℝ) ^ (-σ₁)) →
    Summable
      (fun n : {n : ℕ // 2 ≤ n} =>
        ‖b n.1‖ * (n.1 : ℝ) ^ (-σ)) ∧
      (∑' n : {n : ℕ // 2 ≤ n},
          ‖b n.1‖ * (n.1 : ℝ) ^ (-σ)) ≤
        (2 : ℝ) ^ (-(σ - σ₁)) *
          ∑' n : {n : ℕ // 2 ≤ n},
            ‖b n.1‖ * (n.1 : ℝ) ^ (-σ₁)

end

end MathlibPlus.Analysis
