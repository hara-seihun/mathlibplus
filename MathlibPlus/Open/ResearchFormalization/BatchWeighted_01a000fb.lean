import Mathlib

namespace MathlibPlus.Open

/-- Inclusion-minimal nonempty member of a finite ordinary family. -/
def inclusionMinimalNonempty {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) : Prop :=
  M ∈ F ∧ M.Nonempty ∧
    ∀ N ∈ F, N.Nonempty → N ⊆ M → N = M

/-- The weighted three-minimum carrier-fibre criterion, with all displayed
    scalar quantities retained in the statement. -/
def weighted_three_minimum_carrier_criterion
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (M₁ M₂ M₃ : Finset α)
    (d₁ d₂ d₃ : ℕ)
    (lam₁ lam₂ lam₃ : ℝ) : Prop := by
  let a₁ : ℝ := lam₁ / (d₁ : ℝ)
  let a₂ : ℝ := lam₂ / (d₂ : ℝ)
  let a₃ : ℝ := lam₃ / (d₃ : ℝ)
  let ρ₁ : ℝ := min (min (min
      (1 - 2 * lam₁ + 2 * a₁)
      (2 * (lam₂ - lam₁ + 2 * a₁)))
      (2 * (lam₃ - lam₁ + 2 * a₁)))
      (1 - 4 * lam₁ + 6 * a₁)
  let ρ₂ : ℝ := min (min (min
      (1 - 2 * lam₂ + 2 * a₂)
      (2 * (lam₁ - lam₂ + 2 * a₂)))
      (2 * (lam₃ - lam₂ + 2 * a₂)))
      (1 - 4 * lam₂ + 6 * a₂)
  let ρ₃ : ℝ := min (min (min
      (1 - 2 * lam₃ + 2 * a₃)
      (2 * (lam₁ - lam₃ + 2 * a₃)))
      (2 * (lam₂ - lam₃ + 2 * a₃)))
      (1 - 4 * lam₃ + 6 * a₃)
  let s₁ : ℝ := 2 * (lam₁ + a₂ + a₃) - 1
  let s₂ : ℝ := 2 * (lam₂ + a₁ + a₃) - 1
  let s₃ : ℝ := 2 * (lam₃ + a₁ + a₂) - 1
  let δ₁ : ℝ := max 0 (-s₁)
  let δ₂ : ℝ := max 0 (-s₂)
  let δ₃ : ℝ := max 0 (-s₃)
  exact
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
      inclusionMinimalNonempty F M₁ ∧
      inclusionMinimalNonempty F M₂ ∧
      inclusionMinimalNonempty F M₃ ∧
      Disjoint M₁ M₂ ∧ Disjoint M₁ M₃ ∧ Disjoint M₂ M₃ ∧
      (∀ N : Finset α,
        inclusionMinimalNonempty F N ↔
          N = M₁ ∨ N = M₂ ∨ N = M₃) ∧
      M₁.card = d₁ ∧ M₂.card = d₂ ∧ M₃.card = d₃ ∧
      3 ≤ d₁ ∧ 3 ≤ d₂ ∧ 3 ≤ d₃ ∧
      (1 / 4 : ℝ) ≤ lam₁ ∧ lam₁ ≤ (1 / 2 : ℝ) ∧
      (1 / 4 : ℝ) ≤ lam₂ ∧ lam₂ ≤ (1 / 2 : ℝ) ∧
      (1 / 4 : ℝ) ≤ lam₃ ∧ lam₃ ≤ (1 / 2 : ℝ) ∧
      lam₁ + lam₂ + lam₃ = 1 ∧
      ρ₁ ≥ 0 ∧ s₁ + min a₂ a₃ ≥ 0 ∧ ρ₂ ≥ δ₁ ∧ ρ₃ ≥ δ₁ ∧
      ρ₂ ≥ 0 ∧ s₂ + min a₁ a₃ ≥ 0 ∧ ρ₁ ≥ δ₂ ∧ ρ₃ ≥ δ₂ ∧
      ρ₃ ≥ 0 ∧ s₃ + min a₁ a₂ ≥ 0 ∧ ρ₁ ≥ δ₃ ∧ ρ₂ ≥ δ₃ →
      ∃ x ∈ M₁ ∪ M₂ ∪ M₃,
        2 * (F.filter (fun A => x ∈ A)).card ≥ F.card

end MathlibPlus.Open
