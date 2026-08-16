import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

def claim13524_exact_target_rank_physical_source : Prop :=
  ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∀ (σ : ℂ), (σ = 1 ∨ σ = -1) →
      let d : ℝ := 2 + x
      let splitMem : (ℝ → ℂ) → Prop := fun f =>
        ∃ a b c : ℂ, ∀ U : ℝ,
          f U = a + b * (Real.cosh U : ℂ) + c * (Real.sinh U : ℂ)
      let compactMem : (ℝ → ℂ) → Prop := fun f =>
        ∃ a b c : ℂ, ∀ Φ : ℝ,
          f Φ = a + b * (Real.cos Φ : ℂ) + c * (Real.sin Φ : ℂ)
      let separationWidth : (ℝ → ℝ → ℂ) → ℕ → Prop := fun R r =>
        ∃ f : Fin r → (ℝ → ℂ), ∃ g : Fin r → (ℝ → ℂ),
          (∀ i, splitMem (f i)) ∧ (∀ i, compactMem (g i)) ∧
            ∀ U Φ : ℝ,
              R U Φ = Finset.sum Finset.univ (fun i => f i U * g i Φ)
      let target : ℝ → ℝ → ℂ := fun U Φ =>
        (d : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ)
      2 ≤ d ∧ d ≤ 3 ∧
        (∀ κ : ℂ, κ ≠ 0 →
          separationWidth
            (fun U Φ =>
              (d : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ) +
                σ * κ * (Real.sinh U : ℂ) * (Real.sin Φ : ℂ)) 3 ∧
          ¬ separationWidth
            (fun U Φ =>
              (d : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ) +
                σ * κ * (Real.sinh U : ℂ) * (Real.sin Φ : ℂ)) 2) ∧
        separationWidth target 2 ∧ ¬ separationWidth target 1 ∧
          (-2 : ℝ) * d ≠ 0

end MathlibPlus.Open.ResearchFormalization
