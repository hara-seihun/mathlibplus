import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section
open scoped BigOperators

/--
The prime-independent local coefficient law forces all coefficients to vanish
for a nonzero reflection-invariant meromorphic carrier, and therefore cannot
be the all-prime von Mangoldt law for a nonconstant carrier.
-/
def primeIndependentCoefficientLaw : Prop :=
  let admissible :
      (ℂ → ℂ) → (ℂ → ℂ) → (ℂ → ℂ) → (ℕ+ → ℂ) → Prop :=
    fun R W L ω =>
      R ≠ 0 ∧
      Meromorphic R ∧
      (∀ s : ℂ, R s = R (1 - s)) ∧
      (∀ s : ℂ, 1 < s.re → R s ≠ 0) ∧
      AnalyticOnNhd ℂ W (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball 0 1, W z ≠ 0) ∧
      W 0 = 1 ∧
      AnalyticOnNhd ℂ L (Metric.ball 0 1) ∧
      L 0 = 0 ∧
      (∀ z ∈ Metric.ball 0 1,
        Complex.exp (L z) = W z) ∧
      (∀ z ∈ Metric.ball 0 1,
        HasSum (fun k : ℕ+ => (ω k / (k : ℂ)) * z ^ (k : ℕ)) (L z)) ∧
      (∀ s : ℂ, 1 < s.re →
        -deriv R s / R s =
          ∑' p : {p : ℕ // Nat.Prime p},
            ∑' k : ℕ+,
              ω k * (Real.log (p : ℝ) : ℂ) *
                Complex.cpow (p : ℂ) (-((k : ℂ) * s)))
  (∀ (R : ℂ → ℂ) (ω : ℕ+ → ℂ),
      (∃ W L : ℂ → ℂ, admissible R W L ω) →
        ((∀ k : ℕ+, ω k = 0) ∧ ∃ c : ℂ, ∀ s : ℂ, R s = c)) ∧
    ¬ ∃ (R : ℂ → ℂ) (ω : ℕ+ → ℂ),
      (∃ W L : ℂ → ℂ, admissible R W L ω) ∧
      (∀ k : ℕ+, ω k = 1) ∧
      ¬ ∃ c : ℂ, ∀ s : ℂ, R s = c

end
end MathlibPlus.Open.Analysis
