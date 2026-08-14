import Mathlib

namespace MathlibPlus.Open.Research.PoissonTuran

open scoped BigOperators

noncomputable section

noncomputable def poissonTuranSummand (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (u n * u (n + 2) - u (n + 1) ^ 2) * x ^ n /
    (Nat.factorial n : ℝ)

noncomputable def poissonTuranFunctional (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ∑' n : ℕ, poissonTuranSummand u x n

/-- Claim 15683. -/
def all_order_poisson_turan_functional : Prop :=
  ∀ (u : ℕ → ℝ) (x : ℝ),
    Summable (poissonTuranSummand u x) →
      poissonTuranFunctional u x =
        Real.exp (-x) * ∑' n : ℕ,
          (u n * u (n + 2) - u (n + 1) ^ 2) * x ^ n /
            (Nat.factorial n : ℝ)

end

end MathlibPlus.Open.Research.PoissonTuran
