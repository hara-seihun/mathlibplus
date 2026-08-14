import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact admitted characterization of perturbation budgets preserving positive,
strictly bridge-minimal margins, including the stated numerical instance. -/
def asymmetricMarginBudgetCharacterization : Prop :=
  let m_f : ℝ := 0.0013129967192460183142
  let m_b : ℝ := 0.000058093232689233683405437434725615050248801708221435546875
  let m_t : ℝ := 0.009385823867106693485628209921570239
  let preserves : ℝ → ℝ → ℝ → Prop := fun ε_f ε_b ε_t =>
    ∀ δ_f δ_b δ_t : ℝ,
      |δ_f| ≤ ε_f →
      |δ_b| ≤ ε_b →
      |δ_t| ≤ ε_t →
      0 < m_f + δ_f ∧
      0 < m_b + δ_b ∧
      0 < m_t + δ_t ∧
      m_b + δ_b < m_f + δ_f ∧
      m_b + δ_b < m_t + δ_t
  let fiveInequalities : ℝ → ℝ → ℝ → Prop := fun ε_f ε_b ε_t =>
    ε_f < m_f ∧
    ε_b < m_b ∧
    ε_t < m_t ∧
    ε_b + ε_f < m_f - m_b ∧
    ε_b + ε_t < m_t - m_b
  (∀ ε_f ε_b ε_t : ℝ,
      0 ≤ ε_f →
      0 ≤ ε_b →
      0 ≤ ε_t →
      (preserves ε_f ε_b ε_t ↔ fiveInequalities ε_f ε_b ε_t)) ∧
    (fiveInequalities ((1 : ℝ) / 1000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000) ∧
      preserves ((1 : ℝ) / 1000) ((1 : ℝ) / 1000000) ((1 : ℝ) / 1000))

end MathlibPlus.Open.Analysis
