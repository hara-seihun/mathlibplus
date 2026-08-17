import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0121

noncomputable section

/-- Claim 18096: a pointwise convergent nonnegative backward-sample sum is
nonincreasing on the positive x-domain, for the normalized gamma carrier H. -/
def backwardSampleSumsNonincreasing_18096 : Prop :=
  let M : ℝ → ℝ := fun t =>
    Real.rpow Real.pi (t / 2) * Real.Gamma ((5 : ℝ) / 4 - t / 2) /
      Real.Gamma ((5 : ℝ) / 4)
  let H : ℝ → ℝ → ℝ := fun x t => Real.rpow x t * M t
  ∀ a : ℕ → ℝ,
    (∀ k : ℕ, 0 ≤ a k) →
      (∀ x : ℝ, 0 < x →
        Summable (fun k : ℕ => a k * H x (-2 * (k : ℝ)))) →
      ∀ ⦃x y : ℝ⦄, 0 < x → 0 < y → x ≤ y →
        (∑' k : ℕ, a k * H y (-2 * (k : ℝ))) ≤
          ∑' k : ℕ, a k * H x (-2 * (k : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.R0121
