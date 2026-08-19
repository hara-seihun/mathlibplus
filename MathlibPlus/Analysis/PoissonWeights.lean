import Mathlib

namespace MathlibPlus.Analysis.PoissonWeights

noncomputable section

/-- Claim 4405: the Poisson weights and all displayed neighboring-weight
identities, with their exact nonnegative and positive domains. -/
def poissonWeightIdentities : Prop :=
  let p : ℕ → ℝ → ℝ :=
    fun n x => Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)
  (∀ x : ℝ, p 0 x = Real.exp (-x)) ∧
    (∀ (n : ℕ) (x : ℝ),
      p (n + 1) x = x / (n + 1) * p n x) ∧
    (∀ (n : ℕ) (x : ℝ), 0 ≤ x → 0 ≤ p n x) ∧
    (∀ (n : ℕ) (x : ℝ), 0 < x → 0 < p n x) ∧
    (∀ (n : ℕ) (x : ℝ), 0 < x → 0 < n →
      p (n - 1) x = n / x * p n x) ∧
    (∀ (n : ℕ) (x : ℝ), 0 < x → 0 < n →
      p n x + p (n - 1) x = (1 + n / x) * p n x)

end

end MathlibPlus.Analysis.PoissonWeights
