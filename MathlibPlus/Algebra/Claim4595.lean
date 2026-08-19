import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 4595: explicit scale-free quadratic witness and endpoint-cofactor
arithmetic.  The order-two PF condition is retained as the concrete
coefficient inequality for this three-term sequence. -/
theorem claim4595_scaleFreePF2Witness (t : ℝ) (ht : 0 < t) :
    let α : ℝ := 1 / 4
    let a₀ : ℝ := 1
    let a₁ : ℝ := t / 2
    let a₂ : ℝ := t ^ 2 / 4
    let Δ₀ : ℝ := t ^ 3 / 32
    let Δ₁ : ℝ := t ^ 3 * (t + 8) / 64
    let Δ₂ : ℝ := t ^ 4 / 16
    let F : ℝ → ℝ := fun z => a₀ + a₁ * z + a₂ * z ^ 2
    (0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ a₂ ∧ a₁ ^ 2 ≥ a₀ * a₂) ∧
      F 0 = 1 ∧
      α * a₁ / a₀ = t / 8 ∧
      (Δ₀ = t ^ 3 / 32 ∧ Δ₁ = t ^ 3 * (t + 8) / 64 ∧
        Δ₂ = t ^ 4 / 16) ∧
      Δ₀ - α * Δ₁ = -t ^ 4 / 256 ∧
      Δ₁ - α * Δ₂ = t ^ 3 / 8 ∧
      Δ₀ - α * Δ₁ < 0 ∧ 0 < Δ₁ - α * Δ₂ := by
  dsimp
  constructor
  · constructor
    · norm_num
    constructor
    · positivity
    constructor
    · positivity
    · nlinarith
  constructor
  · norm_num
  constructor
  · ring
  constructor
  · refine ⟨by ring, by ring, by ring⟩
  constructor
  · ring
  constructor
  · ring
  · constructor
    · have h4 : 0 < t ^ 4 := pow_pos ht 4
      nlinarith
    · have h3 : 0 < t ^ 3 := pow_pos ht 3
      nlinarith

/-- The first-mass obstruction persists below every positive threshold. -/
theorem claim4595_no_smallness_threshold :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧
      t / 8 < ε ∧
      0 ≤ (1 : ℝ) ∧ 0 ≤ t / 2 ∧ 0 ≤ t ^ 2 / 4 ∧
      (t / 2) ^ 2 ≥ (1 : ℝ) * (t ^ 2 / 4) ∧
      -(t ^ 4) / 256 < 0 := by
  intro ε hε
  refine ⟨4 * ε, by positivity, ?_, by norm_num, by positivity, by positivity, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h4 : 0 < (4 * ε) ^ 4 := pow_pos (by positivity) 4
    nlinarith

end MathlibPlus.Algebra
