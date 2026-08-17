import MathlibPlus.Open.Analysis.TransferableMultiplierLimitsForceCoreDivergence

namespace MathlibPlus.Open.Analysis.Claim11993

noncomputable section

private def localUniformOnDisks
    (M : ℕ → ℂ → ℂ) (s : ℕ → ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ ≤ R → ‖M (s n) z - F z‖ < ε

/-- Claim 11993: for the exact increasing-order exponential multipliers,
local-uniform subsequential convergence is equivalent to vanishing root scale,
and the only entire limit is one. -/
def claim11993 : Prop :=
  ∀ (k : ℕ → ℕ) (α : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n : ℕ, 0 < k n) →
    (∀ n : ℕ, 0 < α n) →
    let a : ℕ → ℝ := fun n =>
      Real.rpow (α n) (1 / (2 * (k n : ℝ)))
    let M : ℕ → ℂ → ℂ := fun n z =>
      Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))
    ∀ (s : ℕ → ℕ), StrictMono s →
      Filter.Tendsto s Filter.atTop Filter.atTop →
      ((∃ F : ℂ → ℂ,
          Differentiable ℂ F ∧
            localUniformOnDisks M s F) ↔
        Filter.Tendsto (fun n : ℕ => a (s n))
          Filter.atTop (nhds 0)) ∧
      (∀ F : ℂ → ℂ,
        Differentiable ℂ F →
          localUniformOnDisks M s F →
            F = (fun _ : ℂ => (1 : ℂ)))

end

end MathlibPlus.Open.Analysis.Claim11993
