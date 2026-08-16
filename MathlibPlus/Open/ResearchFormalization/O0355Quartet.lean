import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0355

/-- Claim 15615: the prescribed irrational off-critical symmetric quartet is
closed under conjugation and under the reflection `s ↦ 1 - s`. -/
def claim15615_fixed_symmetric_quartet : Prop :=
  ∀ (α : ℝ), Irrational α → 0 < α → α < 1 / 2 →
    ∀ (m : ℕ), 1 ≤ m →
      ∀ (τ : ℝ), 0 < τ →
        let η : ℂ := (α : ℂ) - (τ : ℂ) * Complex.I
        let ρ : ℂ := 1 - η
        let A : Set ℂ :=
          {η, starRingEnd ℂ η, ρ, starRingEnd ℂ ρ}
        A.ncard = 4 ∧
          (∀ z ∈ A, starRingEnd ℂ z ∈ A) ∧
          (∀ z ∈ A, 1 - z ∈ A) ∧
          (∀ z ∈ A, z.re ≠ (1 / 2 : ℝ))

end MathlibPlus.Open.ResearchFormalization.O0355
