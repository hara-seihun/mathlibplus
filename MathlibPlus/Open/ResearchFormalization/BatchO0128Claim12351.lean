import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchO0128

/-- Pure Gaussian positivity and normalized confluent trace determinants. -/
def claim12351 : Prop :=
  ∀ (a : ℝ), 0 < a →
    let F : ℝ → ℝ := fun t => Real.exp (-a * t ^ 2)
    ∀ (m : ℕ), 1 ≤ m →
      let Hₘ : ℝ → ℝ := fun t =>
        (-1 : ℝ) ^ (m * (m - 1) / 2) *
          Matrix.det (fun i j : Fin m =>
            iteratedDeriv (i.1 + j.1) F t)
      Hₘ 0 ≠ 0 ∧
        ∀ t : ℝ, Hₘ t / Hₘ 0 = Real.exp (-(m : ℝ) * a * t ^ 2)

end MathlibPlus.Open.ResearchFormalization.BatchO0128
