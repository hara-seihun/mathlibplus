import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The constant channel from the admitted claim. -/
noncomputable def constantChannel (lambda mu : ℝ) : ℝ :=
  -(2 * Real.log Real.pi) / (lambda + mu)

/-- Strict negative definiteness on every finite set of distinct positive nodes. -/
def constantChannelStrictlyNegativeDefinite : Prop :=
  ∀ (n : ℕ) (nodes : Fin n → ℝ),
    (∀ i, 0 < nodes i) →
    Function.Injective nodes →
    ∀ coefficients : Fin n → ℝ,
      (∃ i, coefficients i ≠ 0) →
      ∑ i, ∑ j,
          coefficients i * coefficients j *
            constantChannel (nodes i) (nodes j) < 0

end MathlibPlus.Open.Analysis
