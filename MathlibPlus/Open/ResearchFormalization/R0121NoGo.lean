import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0121

/-- Claim 18098: no nonnegative, convergent backward-orbit expansion can
represent any positive even central derivative throughout the positive
x-domain. -/
noncomputable def noNonnegativeBackwardOrbitConnection_18098 : Prop :=
  let M : ℝ → ℝ := fun t =>
    Real.rpow Real.pi (t / 2) * Real.Gamma ((5 : ℝ) / 4 - t / 2) /
      Real.Gamma ((5 : ℝ) / 4)
  let H : ℝ → ℝ → ℝ := fun x t => Real.rpow x t * M t
  ∀ (j : ℕ), 1 ≤ j →
    ¬ ∃ a : ℕ → ℝ,
      (∀ k : ℕ, 0 ≤ a k) ∧
        (∀ x : ℝ, 0 < x →
          Summable (fun k : ℕ => a k * H x (-2 * (k : ℝ)))) ∧
        (∀ x : ℝ, 0 < x →
          (deriv^[2 * j] (H x)) 0 =
            ∑' k : ℕ, a k * H x (-2 * (k : ℝ)))

end MathlibPlus.Open.ResearchFormalization.R0121
