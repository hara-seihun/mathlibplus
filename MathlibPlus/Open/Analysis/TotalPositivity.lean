import Mathlib

namespace MathlibPlus.Open.Analysis.TotalPositivity

noncomputable section

open Matrix

/-- Claim 380: a positive oriented confluent derivative flag through order `m`
forces strict positivity of every order-`m` translation determinant. -/
def confluentFlagImpliesStrictPF : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (G : ℝ → ℝ),
    ContDiff ℝ (2 * (m - 1)) G →
    (∀ (k : ℕ), 1 ≤ k → k ≤ m → ∀ t : ℝ,
      0 < (-1 : ℝ) ^ (k * (k - 1) / 2) *
        Matrix.det (fun i j : Fin k =>
          iteratedDeriv (i.val + j.val) G t)) →
    ∀ (x y : Fin m → ℝ), StrictMono x → StrictMono y →
      0 < Matrix.det (fun i j : Fin m => G (x i - y j))

end

end MathlibPlus.Open.Analysis.TotalPositivity
