import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The separated-half-plane exponential family from the packet. -/
noncomputable def separatedExponential (n : ℕ) (s₀ s : ℂ) : ℂ :=
  Complex.exp (-((n : ℂ) * (s - s₀)))

/-- Explicit uniform envelopes showing the analytic-continuation amplification. -/
def claim17439 : Prop :=
  ∀ (s₀ : ℂ) (ε : ℝ),
    0 < ε →
      (∀ n : ℕ, Differentiable ℂ (separatedExponential n s₀)) ∧
      Filter.Tendsto
        (fun n : ℕ => Real.exp (-((n : ℝ) * ε)))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n : ℕ => Real.exp ((n : ℝ) * ε))
        Filter.atTop Filter.atTop ∧
      (∀ (n : ℕ) (s : ℂ),
        s₀.re + ε ≤ s.re →
          ‖separatedExponential n s₀ s‖ ≤
            Real.exp (-((n : ℝ) * ε))) ∧
      (∀ (n : ℕ) (s : ℂ),
        s.re ≤ s₀.re - ε →
          Real.exp ((n : ℝ) * ε) ≤
            ‖separatedExponential n s₀ s‖)

end MathlibPlus.Open.ResearchFormalization
